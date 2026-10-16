"""Run certified generators and checkers against actual implementation outputs."""

import argparse
from dataclasses import asdict, dataclass
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

from pbt.lean_tools import rebuild_modules, require_name, require_timeout, run_checked, timeout_output
from pbt.observations import load_config, load_manifest, validate_generated_view
from pbt.verify_observable import verify_observable, fingerprint_dependencies


@dataclass(frozen=True)
class RunOptions:
    manifest: Path
    config: Path
    observation_id: str
    spec_module: str
    view_module: str
    view_namespace: str
    property_module: str
    premise: str
    target: str
    check: str
    check_correct: str
    generator_module: str
    generator: str
    adapter: tuple[str, ...]
    output: Path
    count: int = 100
    size: int = 10
    seed: int = 0
    timeout_seconds: float = 60
    implementation_timeout_seconds: float = 10


@dataclass(frozen=True)
class RunResult:
    status: str
    evaluated: int
    skipped: int
    requested: int
    error: str | None = None


def _write(path: Path, value: object) -> None:
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False, allow_nan=False) + "\n", encoding="utf-8")


def _sampler(options: RunOptions) -> str:
    return f'''import Lean
import {options.view_module}
import {options.generator_module}
open Lean

def main (args : List String) : IO UInt32 := do
  let [countText, sizeText, seedText] := args | return 1
  let some count := countText.toNat? | return 1
  let some size := sizeText.toNat? | return 1
  let some seed := seedText.toNat? | return 1
  for index in [:count] do
    let fields := [("index", toJson index), ("size", toJson size), ("seed", toJson (seed + index))]
    let input : {options.view_namespace}.Input := {options.generator}.val size (seed + index)
    let fields := fields ++ [("input", {options.view_namespace}.encodeInput input)]
    (← IO.getStdout).putStrLn (Json.mkObj fields).compress
  return 0
'''


def _certify_sampler(project: Path, options: RunOptions):
    rebuild_modules(project, ["pbt.Observable", options.view_module, options.property_module,
                              options.generator_module], options.timeout_seconds)
    base = project / ".lake" / "observable"
    base.mkdir(parents=True, exist_ok=True)
    directory = Path(tempfile.mkdtemp(prefix="sampler-", dir=base))
    audit = directory / "Audit.lean"
    audit.write_text(f'''import pbt.Observable
import pbt.CorrectGen
import {options.view_module}
import {options.property_module}
import {options.generator_module}
#spec4pbt_verify {options.generator} in_module {options.generator_module} :
  (Spec4Pbt.CorrectGen ({options.premise} : {options.view_namespace}.Input → Prop))
#spec4pbt_observable_executable {options.generator}
#spec4pbt_observable_transport {options.view_namespace}.encodeInput
''', encoding="utf-8")
    driver = directory / "Driver.lean"
    driver.write_text(_sampler(options), encoding="utf-8")
    fingerprints = fingerprint_dependencies(project, [audit, driver], options.timeout_seconds)
    run_checked(["lake", "env", "lean", str(audit)], project, options.timeout_seconds)
    run_checked(["lake", "env", "lean", "-o", str(directory / "Driver.olean"), str(driver)],
                project, options.timeout_seconds)
    _assert_fresh(fingerprints)
    return driver, fingerprints


def _assert_fresh(fingerprints):
    import hashlib
    for name, expected in fingerprints.items():
        path = Path(name)
        if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise ValueError(f"Certified sampler is stale: {name}; rebuild and verify again")


def _strict_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"Duplicate JSON field {key!r}")
        result[key] = value
    return result


def _reject_constant(value):
    raise ValueError(f"Invalid JSON constant {value!r}")


def _json(text):
    return json.loads(text, object_pairs_hook=_strict_object, parse_constant=_reject_constant)


def run_observable(project: Path, options: RunOptions) -> RunResult:
    project = Path(project).resolve()
    requested_output = project / options.output
    if os.path.lexists(requested_output):
        raise FileExistsError(f"Run output already exists: {requested_output}")
    output = requested_output.resolve()
    for name in ("count", "size", "seed"):
        value = getattr(options, name)
        if type(value) is not int or value < (1 if name == "count" else 0):
            raise ValueError(f"{name} must be {'positive' if name == 'count' else 'nonnegative'} integer")
    require_timeout(options.timeout_seconds)
    require_timeout(options.implementation_timeout_seconds)
    for name in (options.spec_module, options.view_module, options.view_namespace,
                 options.property_module, options.premise, options.target, options.check,
                 options.check_correct, options.generator_module, options.generator):
        require_name(name)
    if (not isinstance(options.adapter, (tuple, list)) or not options.adapter
            or any(not isinstance(arg, str) or not arg or "\x00" in arg for arg in options.adapter)):
        raise ValueError("adapter must be a nonempty command argument array")
    manifest = load_manifest(project / options.manifest)
    configuration = load_config(project / options.config)
    profile = validate_generated_view(project, manifest, configuration,
        options.observation_id, options.spec_module, options.view_module,
        options.view_namespace, options.timeout_seconds)
    sampler, fingerprints = _certify_sampler(project, options)
    checker = verify_observable(project, options.view_module, options.view_namespace,
        options.property_module, options.premise, options.target, options.check,
        options.check_correct, options.timeout_seconds, expected_profile_id=profile)
    # All configuration/type/proof errors occur before publishing a run folder.
    _assert_fresh(fingerprints)
    checker.assert_fresh()
    if profile != validate_generated_view(project, manifest, configuration,
            options.observation_id, options.spec_module, options.view_module,
            options.view_namespace, options.timeout_seconds):
        raise ValueError("Observation profile changed during certification")
    output.mkdir(parents=True, exist_ok=False)
    _write(output / "manifest.json", manifest)
    _write(output / "observations.json", configuration)
    _write(output / "run.json", {
        "profile_id": profile, "checker_identity": checker.identity,
        "options": {key: str(value) if isinstance(value, Path) else value
                    for key, value in asdict(options).items()},
        "sampler_fingerprints": fingerprints,
        "checker_fingerprints": checker.source_fingerprints,
        "cwd": str(project),
    })
    evaluated = 0

    def finish(status, error=None):
        result = RunResult(status, evaluated, 0, options.count, error)
        _write(output / "result.json", asdict(result))
        return result

    try:
        command = ["lake", "env", "lean", "--run", str(sampler),
                   str(options.count), str(options.size), str(options.seed)]
        samples_text = run_checked(command, project, options.timeout_seconds)
        (output / "samples.jsonl").write_text(samples_text, encoding="utf-8")
        _assert_fresh(fingerprints)
        samples = [_json(line) for line in samples_text.splitlines()]
        if len(samples) != options.count:
            raise ValueError(f"Sampler produced {len(samples)} records, expected {options.count}")
        for index, sample in enumerate(samples):
            metadata = {"index": index, "size": options.size, "seed": options.seed + index}
            if (not isinstance(sample, dict) or any(type(sample.get(k)) is not int or sample[k] != v
                    for k, v in metadata.items())):
                raise ValueError(f"Invalid sampler metadata at index {index}: {sample!r}")
            if set(sample) != {*metadata, "input"}:
                raise ValueError(f"Invalid sample at index {index}: {sample!r}")
            case = output / f"case-{index:06d}"
            case.mkdir()
            _write(case / "sample.json", sample)
            request = {"input": sample["input"]}
            _write(case / "request.json", request)
            process = {"command": list(options.adapter), "cwd": str(project),
                       "timeout_seconds": options.implementation_timeout_seconds}
            try:
                completed = subprocess.run(options.adapter, cwd=project, capture_output=True,
                    text=True, input=json.dumps(request, allow_nan=False),
                    timeout=options.implementation_timeout_seconds, check=False)
            except subprocess.TimeoutExpired as error:
                process.update(timeout=True, stdout=timeout_output(error.stdout), stderr=timeout_output(error.stderr))
                raise TimeoutError(f"Implementation timed out after {options.implementation_timeout_seconds}s") from error
            except OSError as error:
                process["error"] = str(error)
                raise
            else:
                process.update(returncode=completed.returncode, stdout=completed.stdout, stderr=completed.stderr)
            finally:
                _write(case / "process.json", process)
            if completed.returncode:
                raise ChildProcessError(f"Implementation exited with status {completed.returncode}")
            response = _json(completed.stdout)
            if not isinstance(response, dict) or set(response) != {"observation"}:
                raise ValueError("Implementation response must contain exactly the observation field")
            _write(case / "observation.json", response)
            # Only the actual observation is evaluated; no spec-produced witness
            # is ever substituted for an implementation result.
            _assert_fresh(fingerprints)
            passed = checker.run(sample["input"], response["observation"])
            evaluated += 1
            _write(case / "verdict.json", {"pass": passed})
            if not passed:
                return finish("failed")
        return finish("passed")
    except (ValueError, OSError, ChildProcessError, TimeoutError, subprocess.TimeoutExpired) as error:
        return finish("error", str(error))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("manifest", "config", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    for name in ("observation-id", "spec-module", "view-module", "view-namespace", "property-module",
                 "premise", "target", "check", "check-correct", "generator-module", "generator"):
        parser.add_argument("--" + name, required=True)
    parser.add_argument("--adapter-command", required=True, help="JSON array of executable and arguments; no shell")
    parser.add_argument("--project", type=Path, default=Path.cwd())
    for name, default in (("count", 100), ("size", 10), ("seed", 0)):
        parser.add_argument("--" + name, type=int, default=default)
    parser.add_argument("--timeout-seconds", type=float, default=60)
    parser.add_argument("--implementation-timeout-seconds", type=float, default=10)
    args = vars(parser.parse_args(argv))
    project = args.pop("project")
    try:
        args["adapter"] = _json(args.pop("adapter_command"))
        result = run_observable(project, RunOptions(**args))
    except (ValueError, OSError, ChildProcessError, TimeoutError) as error:
        print(str(error), file=sys.stderr)
        return 2
    print(json.dumps(asdict(result)))
    return {"passed": 0, "failed": 1, "error": 2}[result.status]


if __name__ == "__main__":
    raise SystemExit(main())
