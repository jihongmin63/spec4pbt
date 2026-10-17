"""Rebuild, certify and execute a user-supplied observable Lean checker.

Certification binds exact declaration names, the view profile, source dependency
closure and local compiled artifacts. Call verify_observable for each PBT run;
its result is an ephemeral capability, not a reusable proof cache.
"""
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

from pbt.lean_tools import rebuild_modules, require_name, require_timeout, run_checked


def _digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fingerprint_dependencies(project: Path, roots: list[Path], timeout: float) -> dict[str, str]:
    """Resolve imports with Lean, retaining the complete local source closure."""
    pending = list(roots)
    result = {}
    for name in ["lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain"]:
        path = project / name
        if path.exists():
            result[str(path)] = _digest(path)
    seen = set()
    while pending:
        path = pending.pop().resolve()
        if path in seen:
            continue
        seen.add(path)
        result[str(path)] = _digest(path)
        sources = run_checked(["lake", "env", "lean", "--src-deps", str(path)], project, timeout)
        for line in sources.splitlines():
            dependency = Path(line).resolve()
            if dependency.is_relative_to(project) and dependency.exists():
                pending.append(dependency)
        objects = run_checked(["lake", "env", "lean", "--deps", str(path)], project, timeout)
        for line in objects.splitlines():
            artifact = Path(line).resolve()
            if artifact.is_file():
                result[str(artifact)] = _digest(artifact)
                if artifact.is_relative_to(project):
                    # Interpreter implementations accompany imported olean files.
                    for suffix in [".ir", ".olean.private", ".olean.server"]:
                        companion = artifact.with_suffix(suffix)
                        if companion.exists():
                            result[str(companion)] = _digest(companion)
    return result


@dataclass(frozen=True)
class CertifiedChecker:
    project: Path
    driver_path: Path
    command: tuple[str, ...]
    profile_id: str
    identity: str
    source_fingerprints: dict[str, str]
    timeout_seconds: float

    def assert_fresh(self) -> None:
        for name, expected in self.source_fingerprints.items():
            path = Path(name)
            if not path.is_file() or _digest(path) != expected:
                raise ValueError(f"Certified checker is stale: {name}; rebuild and verify again")

    def run(self, input_value: object, observation: object, timeout_seconds: float | None = None) -> bool:
        self.assert_fresh()
        timeout = require_timeout(self.timeout_seconds if timeout_seconds is None else timeout_seconds)
        result = subprocess.run(self.command, cwd=self.project, text=True, capture_output=True,
                                input=json.dumps({"input": input_value, "observation": observation}, allow_nan=False),
                                timeout=timeout, check=False)
        if result.returncode:
            raise ChildProcessError(f"Observable checker failed ({result.returncode}): {result.stdout}\n{result.stderr}")
        try:
            reply = json.loads(result.stdout)
        except json.JSONDecodeError as error:
            raise ValueError(f"Malformed checker response: {result.stdout!r}") from error
        if not isinstance(reply, dict) or set(reply) != {"pass"} or type(reply["pass"]) is not bool:
            raise ValueError(f"Malformed checker response: {reply!r}")
        self.assert_fresh()
        return reply["pass"]


def _driver(view_module: str, namespace: str, property_module: str, check: str) -> str:
    return f'''import {view_module}
import {property_module}
open Lean

def observableDecode (text : String) : Except String ({namespace}.Input × {namespace}.Observation) := do
  let value ← _root_.Lean.Json.parse text
  let fields ← value.getObj?
  unless fields.size == 2 do throw "expected exactly input and observation fields"
  let input ← {namespace}.decodeInput (← value.getObjVal? "input")
  let observation ← {namespace}.decodeObservation (← value.getObjVal? "observation")
  return (input, observation)

def observableEvaluate (text : String) : Except String _root_.Lean.Json := do
  let (input, observation) ← observableDecode text
  return _root_.Lean.Json.mkObj [("pass", _root_.Lean.Json.bool (_root_.{check} input observation))]

def main (args : List String) : IO UInt32 := do
  if args == ["--profile-id"] then
    (← IO.getStdout).putStrLn (_root_.Lean.Json.str _root_.{namespace}.profileId).compress
    return 0
  unless args.isEmpty do
    (← IO.getStderr).putStrLn "unexpected checker arguments"
    return 1
  let text ← (← IO.getStdin).readToEnd
  match observableEvaluate text with
  | .error message =>
    (← IO.getStderr).putStrLn message
    return 1
  | .ok result =>
    (← IO.getStdout).putStrLn result.compress
    return 0
'''


def verify_observable(project: Path, view_module: str, view_namespace: str,
                      property_module: str, premise: str, target: str,
                      check: str, check_correct: str, timeout_seconds: float, *,
                      expected_profile_id: str | None = None,
                      output_dir: Path | None = None) -> CertifiedChecker:
    """Build exact safe, axiom-free declarations and a real JSON checker driver.

    All four property declarations must be owned by property_module. The view
    owns Input, Observation and profileId. No Target proof is requested: only
    check_correct's conditional Boolean equivalence is certified. The returned
    command must run with cwd=result.project; run() enforces protocol/freshness.
    """
    project = Path(project).resolve()
    timeout = require_timeout(timeout_seconds)
    for name in [view_module, view_namespace, property_module, premise, target, check, check_correct]:
        require_name(name)
    rebuild_modules(project, ["pbt.Observable", view_module, property_module], timeout)
    base = Path(output_dir).resolve() if output_dir is not None else project / ".lake" / "observable"
    base.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="certified-", dir=base))
    audit_path = directory / "Audit.lean"
    declarations = [
        (view_namespace + ".Input", view_module, "Type"),
        (view_namespace + ".Observation", view_module, "Type"),
        (view_namespace + ".profileId", view_module, "String"),
        (premise, property_module, f"{view_namespace}.Input → Prop"),
        (target, property_module, f"{view_namespace}.Input → {view_namespace}.Observation → Prop"),
        (check, property_module, f"{view_namespace}.Input → {view_namespace}.Observation → Bool"),
        (check_correct, property_module,
         f"∀ (i : {view_namespace}.Input) (o : {view_namespace}.Observation), "
         f"{premise} i → ({check} i o = true ↔ {target} i o)"),
    ]
    transport = [
        (view_namespace + ".encodeInput", f"{view_namespace}.Input → Lean.Json"),
        (view_namespace + ".decodeInput", f"Lean.Json → Except String {view_namespace}.Input"),
        (view_namespace + ".decodeObservation", f"Lean.Json → Except String {view_namespace}.Observation"),
    ]
    audit_path.write_text(f"import pbt.Observable\nimport {view_module}\nimport {property_module}\n" + "\n".join(
        f"#spec4pbt_verify {name} in_module {module} : ({expected})\n"
        f"#spec4pbt_observable_audit {name}" for name, module, expected in declarations
    ) + f"\n#spec4pbt_observable_executable {check}\n" + "\n".join(
        f"#spec4pbt_observable_transport_type {name} in_module {view_module} : ({expected})" for name, expected in transport
    ) + "\n", encoding="utf-8")
    driver_path = directory / "Driver.lean"
    driver_path.write_text(_driver(view_module, view_namespace, property_module, check), encoding="utf-8")
    fingerprints = fingerprint_dependencies(project, [audit_path, driver_path], timeout)
    run_checked(["lake", "env", "lean", str(audit_path)], project, timeout)
    # Lean compiles executable definitions during elaboration; --run also loads
    # their interpreter implementations, detecting missing executable code.
    run_checked(["lake", "env", "lean", "-o", str(directory / "Driver.olean"), str(driver_path)], project, timeout)
    command = ("lake", "env", "lean", "--run", str(driver_path))
    output = run_checked([*command, "--profile-id"], project, timeout)
    try:
        profile_id = json.loads(output)
    except json.JSONDecodeError as error:
        raise ValueError(f"Malformed view profile identity: {output!r}") from error
    if not isinstance(profile_id, str) or not profile_id:
        raise ValueError("View profileId must be a nonempty String")
    if expected_profile_id is not None and profile_id != expected_profile_id:
        raise ValueError(f"Observation profile mismatch: expected {expected_profile_id!r}, got {profile_id!r}")
    if fingerprints != fingerprint_dependencies(project, [audit_path, driver_path], timeout):
        raise ValueError("Checker sources or compiled dependencies changed during certification")
    identity_payload = {"profile_id": profile_id, "view_module": view_module,
                        "view_namespace": view_namespace, "property_module": property_module,
                        "premise": premise, "target": target, "check": check,
                        "check_correct": check_correct, "files": fingerprints}
    identity = hashlib.sha256(json.dumps(identity_payload, sort_keys=True).encode()).hexdigest()
    (directory / "certificate.json").write_text(json.dumps({**identity_payload, "identity": identity}, indent=2) + "\n")
    return CertifiedChecker(project, driver_path, command, profile_id, identity, fingerprints, timeout)
