#!/usr/bin/env python3
"""Deterministic independent inspection for the Cedar experiment.

This module replaces the former LLM Inspector role.  It has two entry points:

* ``inspect_candidate`` runs before a candidate is measured.  It checks the
  staged snapshot against the adopted chain and frozen hashes, then repeats the
  syntax gate, the whole equivalence chain with its assumption audit, and a
  short official-scheduler derivation on a fresh copy that contains only the
  ``.v`` sources.  It finally confirms that the staged sources and frozen tools
  did not change.
* ``tool_review`` runs once before an experiment.  It executes the complete
  regression suite under ``scripts/tests`` and binds the result to the frozen
  manifest of the exact commit, sources, tools, and conditions.

Every subprocess runs Python with ``-B`` so inspection never writes bytecode
caches into the source tree.  Inspection evidence is append-only.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import time
from typing import Any, Mapping

ROOT = Path(__file__).resolve().parents[2]
PROBE_SEED = 101
PROBE_ATTEMPTS = 20
STEP_TIMEOUT_SECONDS = 3600
TOOL_REVIEW_KIND = "scripted_tool_review"
CANDIDATE_KIND = "scripted_candidate_inspection"
VERSION_RE = re.compile(r"v[0-9]{3}\Z")
UNITTEST_RE = re.compile(r"^Ran (\d+) tests? in [0-9.]+s$", re.MULTILINE)


class InspectionError(RuntimeError):
    """The inspection itself could not run; not a verdict about a candidate."""


def sha256_file(path: Path) -> str:
    if not path.is_file() or path.is_symlink():
        raise InspectionError(f"missing or nonregular file: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def python_env() -> dict[str, str]:
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    return env


def run_step(command: list[str], *, cwd: Path, log: Path,
             timeout: int = STEP_TIMEOUT_SECONDS) -> dict[str, Any]:
    """Run one command, kill its process group on timeout, keep a full log."""
    if log.exists():
        raise InspectionError(f"refusing to overwrite inspection log: {log}")
    started = time.monotonic()
    process = subprocess.Popen(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, env=python_env(),
                               start_new_session=True)
    status = "completed"
    try:
        output, _ = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        output, _ = process.communicate()
        status = "timeout"
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.communicate()
        raise
    log.write_text(output)
    return {"command": command, "status": status, "returncode": process.returncode,
            "seconds": round(time.monotonic() - started, 3), "log": str(log),
            "log_sha256": sha256_file(log)}


def _versions(directory: Path) -> list[str]:
    if not directory.is_dir():
        return []
    names = sorted(path.name for path in directory.iterdir())
    if any(not VERSION_RE.fullmatch(name) for name in names):
        raise InspectionError(f"unexpected candidate directory entry in {directory}")
    return names


def snapshot_violations(staged: Path, chain: Path, version: str,
                        candidate_sha256: str, original_sha256: str) -> list[str]:
    """Compare the staged chain with the adopted chain and frozen hashes."""
    violations = []
    if sha256_file(staged / "Original.v") != original_sha256:
        violations.append("staged Original.v differs from the frozen source")
    adopted = _versions(chain / "candidates")
    staged_versions = _versions(staged / "candidates")
    if staged_versions != adopted + [version]:
        violations.append(f"staged versions {staged_versions} are not adopted "
                          f"{adopted} followed by {version}")
    for name in adopted:
        for filename in ("Candidate.v", "Equivalence.v"):
            old = chain / "candidates" / name / filename
            new = staged / "candidates" / name / filename
            if not new.is_file() or new.read_bytes() != old.read_bytes():
                violations.append(f"staged {name}/{filename} differs from the adopted chain")
    selected = staged / "candidates" / version
    if not (selected / "Candidate.v").is_file():
        violations.append(f"{version}/Candidate.v is missing")
    elif sha256_file(selected / "Candidate.v") != candidate_sha256:
        violations.append(f"{version}/Candidate.v differs from the proved candidate")
    if not (selected / "Equivalence.v").is_file():
        violations.append(f"{version}/Equivalence.v is missing")
    extra = sorted(path.name for path in selected.iterdir()
                   if path.name not in ("Candidate.v", "Equivalence.v")) if selected.is_dir() else []
    if extra:
        violations.append(f"unexpected files in staged {version}: {extra}")
    return violations


def source_inventory(staged: Path) -> dict[str, str]:
    files = [staged / "Original.v", *sorted((staged / "candidates").rglob("*.v"))]
    return {path.relative_to(staged).as_posix(): sha256_file(path) for path in files}


def fresh_copy(staged: Path, destination: Path) -> None:
    """Copy only authored Coq sources; no build product can mask a failure."""
    destination.mkdir(parents=True)
    shutil.copyfile(staged / "Original.v", destination / "Original.v")
    for path in sorted((staged / "candidates").rglob("*.v")):
        target = destination / path.relative_to(staged)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(path, target)


def _json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text())
    except (OSError, json.JSONDecodeError):
        return {}
    return value if isinstance(value, dict) else {}


def inspect_candidate(root: Path, staged: Path, chain: Path, version: str,
                      candidate_sha256: str, frozen: Mapping[str, Any],
                      evidence: Path, *, probe_attempts: int = PROBE_ATTEMPTS) -> dict[str, Any]:
    """Return a passed/failed inspection report and store it in ``evidence``."""
    if not VERSION_RE.fullmatch(version):
        raise InspectionError(f"invalid candidate version: {version}")
    directory = evidence / "inspection"
    directory.mkdir(parents=True)
    report: dict[str, Any] = {"kind": CANDIDATE_KIND, "candidate": version,
                              "status": "running", "checks": [], "violations": [],
                              "commands": []}
    result_path = directory / "result.json"

    def finish(status: str) -> dict[str, Any]:
        report["status"] = status
        result_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
        return report

    def record(name: str, ok: bool, detail: str = "") -> bool:
        report["checks"].append({"name": name, "status": "passed" if ok else "failed",
                                 "detail": detail[:2000]})
        if not ok:
            report["violations"].append(f"{name}: {detail}"[:2000])
        return ok

    original_sha = frozen["sources"]["properties/cedar_no_type_error/Original.v"]
    before = source_inventory(staged)
    tools_before = {name: sha256_file(root / name) for name in frozen["tools"]}
    record("frozen_tools", tools_before == dict(frozen["tools"]),
           "tool hashes differ from the frozen manifest")
    snapshot = snapshot_violations(staged, chain, version, candidate_sha256, original_sha)
    if not record("snapshot", not snapshot, "; ".join(snapshot)):
        return finish("failed")

    fresh = directory / "property"
    fresh_copy(staged, fresh)
    python = [sys.executable, "-B"]
    env_script = str(root / "environment/env.sh")

    syntax_dir = directory / "syntax"
    step = run_step([*python, str(root / "scripts/cedar/syntax.py"), str(fresh),
                     "--candidate", version, "--evidence-dir", str(syntax_dir),
                     "--env-script", env_script], cwd=root, log=directory / "syntax.log")
    report["commands"].append(step)
    syntax = _json(syntax_dir / "result.json")
    if not record("syntax", step["returncode"] == 0 and syntax.get("status") == "passed"
                  and syntax.get("candidate") == version,
                  str(syntax.get("error") or f"syntax.py exit {step['returncode']}")):
        return finish("failed")

    step = run_step([*python, str(root / "scripts/check.py"), str(fresh)],
                    cwd=root, log=directory / "check.log")
    report["commands"].append(step)
    checks = sorted((fresh / ".runs").glob("check-*/result.json"))
    audit = _json(checks[0]) if len(checks) == 1 else {}
    if not record("equivalence_chain",
                  step["returncode"] == 0 and audit.get("status") == "passed"
                  and audit.get("assumptions") == [],
                  str(audit.get("error") or f"check.py exit {step['returncode']}")):
        return finish("failed")

    probe = fresh / ".runs" / f"inspection-benchmark-{version}"
    step = run_step([*python, str(root / "scripts/cedar/benchmark.py"), str(fresh),
                     "--candidate", version, "--seed", str(PROBE_SEED),
                     "--attempts", str(probe_attempts), "--test-mode",
                     "--output-dir", str(probe)], cwd=root, log=directory / "derivation.log")
    report["commands"].append(step)
    bench = _json(probe / "result.json")
    quickchick = (bench.get("quickchick") or {}).get("status")
    if not record("derivation_probe",
                  step["returncode"] == 0 and bench.get("status") == "completed"
                  and (bench.get("derivation") or {}).get("status") == "succeeded"
                  and quickchick in ("passed", "gave_up"),
                  str(bench.get("error") or f"benchmark.py exit {step['returncode']}, "
                      f"internal QuickChick {quickchick}")):
        return finish("failed")
    report["derivation_probe"] = {"result": str(probe / "result.json"),
                                  "quickchick": bench.get("quickchick"),
                                  "counts": bench.get("counts")}

    after = source_inventory(staged)
    tools_after = {name: sha256_file(root / name) for name in frozen["tools"]}
    record("sources_unchanged", after == before, "staged sources changed during inspection")
    record("tools_unchanged", tools_after == tools_before, "tools changed during inspection")
    return finish("passed" if not report["violations"] else "failed")


def check_candidate_report(path: Path, version: str) -> dict[str, Any]:
    """Accept only a complete scripted report with every required check passed."""
    report = _json(path)
    required = ["frozen_tools", "snapshot", "syntax", "equivalence_chain",
                "derivation_probe", "sources_unchanged", "tools_unchanged"]
    names = [check.get("name") for check in report.get("checks", [])]
    if (report.get("kind") != CANDIDATE_KIND or report.get("candidate") != version
            or report.get("status") != "passed" or report.get("violations") != []
            or names != required
            or any(check.get("status") != "passed" for check in report["checks"])):
        raise InspectionError(f"candidate inspection did not pass: {path}")
    for command in report.get("commands", []):
        log = Path(command.get("log", ""))
        if command.get("returncode") != 0 or sha256_file(log) != command.get("log_sha256"):
            raise InspectionError(f"inspection command evidence is missing or changed: {log}")
    return report


def tool_review(root: Path, review_dir: Path, frozen: Mapping[str, Any]) -> Path:
    """Run the full regression suite once and bind it to the frozen manifest."""
    modules = [f"scripts.tests.{path.stem}"
               for path in sorted((root / "scripts/tests").glob("test_*.py"))]
    if not modules:
        raise InspectionError("no regression modules under scripts/tests")
    review_dir.mkdir(parents=True)
    # scripts/ is a namespace package, so modules are named explicitly.
    command = [sys.executable, "-B", "-m", "unittest", *modules]
    step = run_step(command, cwd=root, log=review_dir / "unittest.log", timeout=4 * 3600)
    output = Path(step["log"]).read_text(errors="replace")
    counts = [int(value) for value in UNITTEST_RE.findall(output)]
    passed = (step["status"] == "completed" and step["returncode"] == 0 and len(counts) == 1
              and counts[0] > 0 and re.search(r"^OK(?: \(.*\))?$", output, re.MULTILINE) is not None)
    review = {"kind": TOOL_REVIEW_KIND, "status": "passed" if passed else "failed",
              "frozen": dict(frozen), "tests_run": counts[0] if counts else 0,
              "commands": [step]}
    path = review_dir / "review.json"
    with path.open("x") as stream:
        json.dump(review, stream, indent=2, sort_keys=True)
        stream.write("\n")
    return path


def check_tool_review(path: Path, frozen: Mapping[str, Any]) -> dict[str, Any]:
    review = _json(path)
    if review.get("kind") != TOOL_REVIEW_KIND or review.get("status") != "passed":
        raise InspectionError(f"scripted tool review did not pass: {path}")
    if review.get("frozen") != frozen:
        raise InspectionError("tool review is not bound to exact frozen hashes/commit")
    commands = review.get("commands") or []
    if len(commands) != 1 or commands[0].get("returncode") != 0 or review.get("tests_run", 0) <= 0:
        raise InspectionError("tool review lacks a successful regression run")
    log = Path(commands[0].get("log", ""))
    if not log.is_file() or log.parent != path.parent or sha256_file(log) != commands[0].get("log_sha256"):
        raise InspectionError("tool review regression log is missing or changed")
    return review


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="action", required=True)
    review = sub.add_parser("tool-review", help="run the regression suite for the frozen tools")
    review.add_argument("--output-dir", required=True, type=Path,
                        help="new directory under properties/cedar_no_type_error/.runs/")
    args = parser.parse_args()
    if __package__ in (None, ""):
        sys.path.insert(0, str(ROOT))
    from scripts.cedar import execute
    output = args.output_dir.resolve()
    if not output.is_relative_to(execute.PROPERTY / ".runs"):
        parser.error("output must be inside the property-local .runs directory")
    path = tool_review(ROOT, output, execute.frozen_manifest(ROOT))
    status = _json(path).get("status")
    print(path)
    return 0 if status == "passed" else 1


if __name__ == "__main__":
    raise SystemExit(main())
