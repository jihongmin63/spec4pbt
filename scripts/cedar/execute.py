#!/usr/bin/env python3
"""Fail-closed coordinator for the fixed Cedar predicate experiment.

All model calls pass through roles.run_role; only the Reformulator and Prover
are model roles. A passed scripted tool review bound to the exact source,
tools, conditions, and commit is required before the first benchmark, and
each candidate passes the scripted independent inspection in inspection.py
before measurement. No old role session is ever resumed.
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
from concurrent.futures import ThreadPoolExecutor
from typing import Any, Mapping

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.cedar import benchmark, experiment, inspection, roles, validator


ROOT = Path(__file__).resolve().parents[2]
PROPERTY = ROOT / "properties/cedar_no_type_error"
SWITCH = Path("/workspace/spec4pbt/_opam-testing-theorems")
SOURCE_FILES = ("specification/cedar/Spec.v", "properties/cedar_no_type_error/Original.v")
TOOL_FILES = (
    "AGENTS.md", "prompts/cedar-experiments.txt",
    "specification/cedar/upstream/Cedar.v.txt",
    "properties/cedar_no_type_error/upstream/CedarWellTypedTermGenerator.v.txt",
    "environment/env.sh", "environment/opam-switch.export",
    "scripts/check.py", "scripts/run.py", "scripts/cedar/execute.py",
    "scripts/cedar/experiment.py", "scripts/cedar/roles.py",
    "scripts/cedar/benchmark.py", "scripts/cedar/syntax.py",
    "scripts/cedar/validator.py", "scripts/cedar/Validator.v",
    "scripts/cedar/Support.v", "scripts/cedar/driver.ml",
    "scripts/cedar/serialization.py",
    *(f"scripts/cedar/prompts/{name}.txt" for name in roles.EFFORT),
    *(f"scripts/cedar/schemas/{name}.json" for name in roles.EFFORT),
)
SAFE_ID = re.compile(r"[A-Za-z][A-Za-z0-9_-]*\Z")
SEED_WORKERS = 5
TOOL_SUFFIXES = {".py", ".v", ".ml", ".md", ".json", ".txt"}


class ExecutionError(RuntimeError):
    """A failed gate or an operational failure; no unsupported result is adopted."""


class ProposalRejected(ExecutionError):
    """A submitted predicate failed its own syntax/proof/derivation path."""


def digest(path: Path) -> str:
    if not path.is_file() or path.is_symlink():
        raise ExecutionError(f"missing or nonregular frozen file: {path}")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def tool_files(root: Path) -> tuple[str, ...]:
    """Freeze every authored script, regression, and Cedar tool document."""
    discovered = {path.relative_to(root).as_posix()
                  for path in (root / "scripts").rglob("*")
                  if path.is_file() and path.suffix in TOOL_SUFFIXES}
    return tuple(sorted(set(TOOL_FILES) | discovered))


def write_new(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x") as stream:
        json.dump(data, stream, indent=2, sort_keys=True)
        stream.write("\n")


def save_state(path: Path, state: Mapping[str, Any]) -> None:
    """Atomic current-state checkpoint; earlier stage records are immutable."""
    temporary = path.with_name(path.name + ".next")
    with temporary.open("x") as stream:
        json.dump(state, stream, indent=2, sort_keys=True)
        stream.write("\n")
    temporary.replace(path)


def frozen_manifest(root: Path = ROOT) -> dict[str, Any]:
    source_hashes = {name: digest(root / name) for name in SOURCE_FILES}
    tool_hashes = {name: digest(root / name) for name in tool_files(root)}
    commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=root, text=True,
                            capture_output=True, check=True).stdout.strip()
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ExecutionError("unable to freeze source commit")
    return {"commit": commit, "sources": source_hashes, "tools": tool_hashes,
            "conditions": {"size": experiment.SIZE,
                           "attempts_per_seed": experiment.ATTEMPTS_PER_SEED,
                           "eval_seeds": list(experiment.EVAL_SEEDS),
                           "held_out_seeds": list(experiment.HELD_OUT_SEEDS),
                           "runs": list(experiment.RUN_IDS),
                           "max_proposals_per_run": experiment.MAX_PROPOSALS,
                           "model": roles.MODEL, "effort": roles.EFFORT,
                           "coq_version": "8.20.0", "ocaml_version": "4.14.2",
                           "seed_workers": SEED_WORKERS,
                           "validator": {"proof_depth": validator.PROOF_DEPTH,
                                         "tactic_timeout_seconds": validator.TACTIC_TIMEOUT_SECONDS,
                                         "batch_timeout_seconds": validator.MAX_BATCH_SECONDS,
                                         "batch_size": validator.DEFAULT_BATCH_SIZE,
                                         "batch_workers": validator.DEFAULT_BATCH_WORKERS}}}


def assert_frozen(root: Path, frozen: Mapping[str, Any]) -> None:
    current = frozen_manifest(root)
    if current != frozen:
        raise ExecutionError("frozen source, tool, environment, conditions, or commit changed")


def ensure_runtime_bridge(root: Path, installed_switch: Path = SWITCH) -> Path:
    """Select the existing pinned installation without copying or modifying it."""
    installed = installed_switch.resolve(strict=True)
    if installed.name != "_opam-testing-theorems" or not (installed / "_opam/bin/coqc").is_file():
        raise ExecutionError("pinned Testing Theorems installation is unavailable")
    local = root / "_opam-testing-theorems"
    if local.is_symlink():
        if local.resolve(strict=True) != installed:
            raise ExecutionError("snapshot switch link does not target pinned installation")
    elif local.exists():
        if local.resolve(strict=True) != installed:
            raise ExecutionError("snapshot has a different local switch")
    else:
        local.symlink_to(installed, target_is_directory=True)
    return local


def _inside(path: Path, ancestor: Path) -> bool:
    try:
        path.resolve(strict=True).relative_to(ancestor.resolve(strict=True))
    except (ValueError, FileNotFoundError):
        return False
    return True


def review_gate(review_path: Path, frozen: Mapping[str, Any],
                property_root: Path = PROPERTY) -> dict[str, Any]:
    """Accept only a passed scripted tool review of the exact frozen manifest."""
    private = property_root / ".runs"
    if not _inside(review_path, private):
        raise ExecutionError("tool review must be property-local private evidence")
    try:
        return inspection.check_tool_review(review_path, frozen)
    except inspection.InspectionError as error:
        raise ExecutionError(str(error)) from error


def role_inputs(root: Path, chain: Path, *, candidate: Path | None = None,
                selected: str | None = None) -> dict[str, Path]:
    bundle = {"specification/cedar/Spec.v": root / SOURCE_FILES[0],
              "property/Original.v": chain / "Original.v"}
    if (chain / "candidates").is_dir():
        for name in sorted((chain / "candidates").iterdir()):
            if not name.is_dir() or not re.fullmatch(r"v[0-9]{3}", name.name):
                raise ExecutionError("unexpected adopted chain entry")
            bundle[f"property/candidates/{name.name}/Candidate.v"] = name / "Candidate.v"
            # Prior Equivalence files are not needed by either authoring role.
    if candidate is not None:
        if selected is None:
            raise ExecutionError("candidate bundle needs a selected version")
        bundle["Candidate.v"] = candidate
        bundle[f"property/candidates/{selected}/Candidate.v"] = candidate
    return bundle


def _forbidden(root: Path, own_run: Path, experiment_dir: Path) -> list[Path]:
    """Probe sibling run sources/private events without exposing them to roles."""
    paths = [root / "AGENTS.md"]
    for sibling in experiment.RUN_IDS:
        path = experiment_dir / sibling
        if path != own_run and (path / "Original.v").exists():
            paths.append(path / "Original.v")
    return paths


def call_role(role: str, root: Path, evidence: Path, inputs: Mapping[str, Path],
              context: Mapping[str, Any], own_run: Path, chains_root: Path) -> dict[str, Any]:
    return roles.run_role(role, root, evidence, inputs, context,
                          forbidden_paths=_forbidden(root, own_run, chains_root),
                          switch=SWITCH)


def checked_command(command: list[str], *, cwd: Path, log: Path,
                    timeout: int = 7200) -> subprocess.CompletedProcess[str]:
    process = subprocess.Popen(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired as error:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        write_new(log, {"command": command, "status": "timeout", "seconds": timeout,
                        "returncode": process.returncode, "stdout": stdout, "stderr": stderr})
        raise ExecutionError(f"command timed out; see {log}") from error
    except BaseException:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        process.communicate()
        raise
    result = subprocess.CompletedProcess(command, process.returncode, stdout, stderr)
    write_new(log, {"command": command, "returncode": result.returncode,
                    "stdout": result.stdout, "stderr": result.stderr})
    return result


def _result(path: Path, expected: str) -> dict[str, Any]:
    if not path.is_file():
        raise ExecutionError(f"missing {expected} result: {path}")
    result = json.loads(path.read_text())
    if result.get("status") != expected:
        raise ExecutionError(f"{path}: status is {result.get('status')!r}, expected {expected}")
    return result


def syntax_check(root: Path, staged: Path, version: str, evidence: Path,
                 frozen: Mapping[str, Any]) -> tuple[bool, str]:
    assert_frozen(root, frozen)
    syntax_dir = evidence / "syntax"
    command = [sys.executable, str(root / "scripts/cedar/syntax.py"), str(staged),
               "--candidate", version, "--evidence-dir", str(syntax_dir),
               "--env-script", str(root / "environment/env.sh")]
    result = checked_command(command, cwd=root, log=evidence / "syntax-command.json")
    report = json.loads((syntax_dir / "result.json").read_text()) if (syntax_dir / "result.json").is_file() else {}
    if result.returncode not in (0, 1) or report.get("status") not in ("passed", "failed"):
        raise ExecutionError("syntax tool failed without a conclusive result")
    if (result.returncode == 0) != (report["status"] == "passed") or report.get("candidate") != version:
        raise ExecutionError("syntax exit status, result, or candidate disagree")
    hashes = report.get("source_hashes") or {}
    expected_hashes = {"property/Original.v": digest(staged / "Original.v"),
                       "specification/cedar/Spec.v": frozen["sources"][SOURCE_FILES[0]]}
    for source in (staged / "candidates").rglob("Candidate.v"):
        key = f"property/{source.relative_to(staged).as_posix()}"
        expected_hashes[key] = digest(source)
    for key, value in hashes.items():
        if key in expected_hashes and value != expected_hashes[key]:
            raise ExecutionError(f"syntax result source hash differs: {key}")
    if report["status"] == "passed" and any(
        hashes.get(key) != value for key, value in expected_hashes.items()
    ):
        raise ExecutionError("passed syntax result lacks exact frozen source hashes")
    return report["status"] == "passed", str(report.get("error") or "syntax rejected")


def prefix_check(root: Path, staged: Path, evidence: Path,
                 frozen: Mapping[str, Any]) -> tuple[bool, str]:
    assert_frozen(root, frozen)
    result = checked_command([sys.executable, str(root / "scripts/check.py"), str(staged)],
                             cwd=root, log=evidence / "prefix-command.json")
    # check.py writes its own proof, assumption-audit, and coqchk result under
    # staged/.runs; the coordinator also stores the command output immutably.
    reports = list((staged / ".runs").glob("check-*/result.json"))
    if len(reports) != 1:
        raise ExecutionError("prefix check did not produce exactly one audit result")
    report = json.loads(reports[0].read_text())
    if (result.returncode == 0) != (report.get("status") == "passed"):
        raise ExecutionError("prefix checker exit status and audit result disagree")
    if result.returncode == 0 and report.get("assumptions") != []:
        raise ExecutionError("prefix check lacks an empty assumption audit")
    return result.returncode == 0, str(report.get("error") or "prefix check failed")


def _batch_rows(path: Path, candidate: str, seed: int) -> list[dict[str, Any]]:
    rows = []
    with path.open() as stream:
        for index, line in enumerate(stream):
            row = json.loads(line)
            if (type(row.get("attempt")) is not int or row["attempt"] != index
                    or row.get("id") != f"{candidate}-{seed}-{index:05d}"
                    or row.get("seed") != seed or "input_coq" not in row
                    or "scheduler_entity_names" not in row):
                raise ExecutionError(f"malformed or missing benchmark attempt {index}: {path}")
            rows.append(row)
    if len(rows) != experiment.ATTEMPTS_PER_SEED:
        raise ExecutionError(f"incomplete benchmark batch: {path}")
    return rows


def check_benchmark_completion(report: Mapping[str, Any], output: Path) -> None:
    """Confirm derivation evidence and the tactic's actual internal result."""
    if report.get("derivation") != {"status": "succeeded", "log": "scheduler.log",
                                     "extracted_checker": "sources/theorem.ml"}:
        raise ExecutionError("completed benchmark lacks derivation evidence")
    if not (output / "sources/theorem.ml").is_file():
        raise ExecutionError("completed benchmark lacks extracted checker")
    scheduler = output / "scheduler.log"
    if not scheduler.is_file():
        raise ExecutionError("completed benchmark lacks scheduler.log")
    contents = scheduler.read_text(errors="replace")
    if "Theorem Schedule:" not in contents or "Pieces:" not in contents:
        raise ExecutionError("completed benchmark lacks official scheduler trace")
    try:
        actual = benchmark.parse_quickchick_result(contents)
    except RuntimeError as error:
        raise ExecutionError(str(error)) from error
    if actual["status"] == "failed" or report.get("quickchick") != actual:
        raise ExecutionError("completed benchmark internal QuickChick outcome disagrees with scheduler.log")


def benchmark_batch(root: Path, staged: Path, candidate: str, seed: int,
                    evidence: Path, frozen: Mapping[str, Any]) -> dict[str, Any]:
    assert_frozen(root, frozen)
    output = staged / ".runs" / f"benchmark-{candidate}-{seed}"
    command = [sys.executable, str(root / "scripts/cedar/benchmark.py"), str(staged),
               "--candidate", candidate, "--seed", str(seed),
               "--output-dir", str(output)]
    process = checked_command(command, cwd=root, log=evidence / f"benchmark-{candidate}-{seed}.json")
    result_path = output / "result.json"
    if not result_path.is_file():
        raise ExecutionError(f"missing benchmark result: {result_path}")
    report = json.loads(result_path.read_text())
    if report.get("status") not in ("completed", "failed"):
        raise ExecutionError("benchmark supplied no conclusive status")
    if (report.get("candidate") != candidate
            or report.get("seed") != seed or report.get("attempts") != experiment.ATTEMPTS_PER_SEED
            or report.get("size") != experiment.SIZE or report.get("test_mode") is not False):
        raise ExecutionError("benchmark status or fixed execution conditions disagree")
    source_hashes = report.get("source_hashes") or {}
    if source_hashes.get("Original.v") != digest(staged / "Original.v") or source_hashes.get("Spec.v") != frozen["sources"][SOURCE_FILES[0]]:
        raise ExecutionError("benchmark fixed source hashes disagree")
    tool_hashes = report.get("tool_hashes") or {}
    for key, name in {"benchmark.py": "scripts/cedar/benchmark.py", "Support.v": "scripts/cedar/Support.v",
                      "driver.ml": "scripts/cedar/driver.ml", "serialization.py": "scripts/cedar/serialization.py",
                      "env.sh": "environment/env.sh"}.items():
        if tool_hashes.get(key) != frozen["tools"][name]:
            raise ExecutionError(f"benchmark tool hash differs: {key}")
    if candidate != "P0" and not report.get("prefix_check"):
        raise ExecutionError("candidate benchmark omitted prefix proof check")
    if report["status"] == "failed":
        if process.returncode == 0 or candidate == "P0":
            raise ExecutionError("baseline failed or benchmark failure exit status disagrees")
        raise ProposalRejected(f"derivation_or_execution_failed: {report.get('error', '')}"[:300])
    if process.returncode:
        raise ExecutionError("completed benchmark result has nonzero exit status")
    check_benchmark_completion(report, output)
    rows = _batch_rows(output / "attempts.jsonl", candidate, seed)
    generated = sum(row["input_coq"] is not None for row in rows)
    if report.get("counts") != {"generated": generated,
                                "discard": len(rows) - generated}:
        raise ExecutionError("benchmark generated/discard counts disagree with raw attempts")
    validator_out = output / "verdicts.jsonl"
    validator_dir = output / "validator-evidence"
    validator_command = [sys.executable, str(root / "scripts/cedar/validator.py"),
                         "--input", str(output / "attempts.jsonl"),
                         "--output", str(validator_out), "--evidence-dir", str(validator_dir),
                         "--env-script", str(root / "environment/env.sh")]
    validated = checked_command(validator_command, cwd=root, log=evidence / f"validator-{candidate}-{seed}.json")
    if validated.returncode:
        raise ExecutionError(f"independent original-predicate validation failed: {validator_out}")
    verdicts = [json.loads(line) for line in validator_out.read_text().splitlines()]
    if len(verdicts) != len(rows):
        raise ExecutionError("validator output count differs from generator attempts")
    counts = {key: 0 for key in experiment.COUNT_KEYS}
    mapping = {"valid": "confirmed_valid", "invalid": "confirmed_invalid",
               "unknown": "undetermined", "no_generation": "no_result"}
    for row, verdict in zip(rows, verdicts):
        if verdict.get("id") != row["id"] or verdict.get("overall") not in mapping:
            raise ExecutionError("validator verdict does not match attempt id")
        expected = (hashlib.sha256(row["input_coq"].encode()).hexdigest()
                    if row["input_coq"] is not None else None)
        if verdict.get("input_sha256") != expected:
            raise ExecutionError("validator verdict does not match full original input")
        counts[mapping[verdict["overall"]]] += 1
    return {"status": "completed", "attempts": len(rows), **counts}


def measure(root: Path, staged: Path, candidate: str, seeds: tuple[int, ...],
            evidence: Path, frozen: Mapping[str, Any]) -> dict[int, dict[str, Any]]:
    if len(set(seeds)) != len(seeds):
        raise ExecutionError("duplicate measurement seed would overwrite evidence")

    def one_seed(seed: int) -> dict[str, Any]:
        counts = benchmark_batch(root, staged, candidate, seed, evidence, frozen)
        write_new(evidence / f"batch-{candidate}-{seed}.json",
                  {"candidate": candidate, "seed": seed, "counts": counts,
                   "benchmark_result": str(staged / ".runs" / f"benchmark-{candidate}-{seed}" / "result.json")})
        return counts

    with ThreadPoolExecutor(max_workers=SEED_WORKERS) as executor:
        futures = {seed: executor.submit(one_seed, seed) for seed in seeds}
        try:
            # Only a full result escapes measure; a failed seed leaves its logs
            # and completed peers' immutable per-seed records for audit.
            return {seed: futures[seed].result() for seed in seeds}
        except BaseException:
            for future in futures.values():
                future.cancel()
            raise


def inspect_candidate(root: Path, staged: Path, chain: Path, version: str,
                      candidate_sha256: str, frozen: Mapping[str, Any],
                      evidence: Path) -> dict[str, Any]:
    """Scripted independent inspection; an inability to inspect stops the run."""
    try:
        return inspection.inspect_candidate(root, staged, chain, version,
                                            candidate_sha256, frozen, evidence)
    except inspection.InspectionError as error:
        raise ExecutionError(f"inspection could not run: {error}") from error


def _stage(run_chain: Path, attempt_dir: Path, version: str, candidate: Path) -> Path:
    staged = attempt_dir / "staged-property"
    staged.mkdir()
    shutil.copyfile(run_chain / "Original.v", staged / "Original.v")
    if (run_chain / "candidates").exists():
        shutil.copytree(run_chain / "candidates", staged / "candidates")
    target = staged / "candidates" / version
    target.mkdir(parents=True)
    shutil.copyfile(candidate, target / "Candidate.v")
    return staged


def _cost(report: Mapping[str, Any] | None) -> dict[str, Any]:
    return dict(report["cost"]) if report is not None else roles.not_run_cost()


def unavailable_cost() -> dict[str, Any]:
    return {"status": "unavailable", "wall_seconds": None,
            "usage": {"status": "unavailable", "input_tokens": None,
                      "output_tokens": None, "cached_input_tokens": None,
                      "reasoning_output_tokens": None}}


def _recorded_role_cost(attempt_dir: Path, role: str) -> dict[str, Any]:
    results = list((attempt_dir / "roles").glob(f"{role}-*/private-evidence/result.json"))
    if len(results) == 1:
        report = json.loads(results[0].read_text())
        if isinstance(report.get("cost"), dict):
            return report["cost"]
    return (unavailable_cost() if (attempt_dir / f"{role}-start.json").is_file()
            else roles.not_run_cost())


def stop_after_error(state: dict[str, Any], evidence: Path, error: Exception) -> None:
    """Count an interrupted proposal and preserve real role costs when available."""
    for run_id in experiment.RUN_IDS:
        run = state["runs"][run_id]
        if run["attempts"] and run["attempts"][-1]["status"] == "pending":
            attempt = run["attempts"][-1]
            attempt_dir = evidence / run_id / attempt["id"]
            candidate_stage = attempt_dir / "candidate-stage.json"
            candidate_sha = (json.loads(candidate_stage.read_text())["candidate_sha256"]
                             if candidate_stage.is_file() else None)
            experiment.finish_attempt(
                state, run_id, attempt["id"], status="rejected",
                reformulation_cost=_recorded_role_cost(attempt_dir, "reformulator"),
                proof_cost=_recorded_role_cost(attempt_dir, "prover"),
                reason=f"operational_failure: {type(error).__name__}: {error}"[:300],
                feedback_summary=f"operational_failure: {type(error).__name__}"[:300],
                candidate_sha256=candidate_sha)
        if run["stop_reason"] is None:
            reason = ("operational_failure" if run["attempts"] else
                      "not_run_due_to_operational_failure")
            experiment.stop_run(state, run_id, reason)


def _finish_failure(state: dict[str, Any], run_id: str, attempt_id: str,
                    reform: Mapping[str, Any] | None, proof: Mapping[str, Any] | None,
                    reason: str, summary: str = "", candidate: Path | None = None,
                    feedback_category: str = "proposal_rejected") -> None:
    experiment.finish_attempt(state, run_id, attempt_id, status="rejected",
                              reformulation_cost=_cost(reform), proof_cost=_cost(proof),
                              reason=reason[:300], feedback_summary=feedback_category,
                              transformation_summary=summary[:300],
                              candidate_sha256=digest(candidate) if candidate is not None else None)


def execute_attempt(root: Path, chain: Path, chains_root: Path, evidence: Path,
                    state: dict[str, Any], run_id: str, frozen: Mapping[str, Any],
                    state_path: Path) -> None:
    assert_frozen(root, frozen)
    attempt_id = experiment.begin_attempt(state, run_id)
    save_state(state_path, state)
    attempt_dir = evidence / run_id / attempt_id
    attempt_dir.mkdir(parents=True)
    version = f"v{len(state['runs'][run_id]['adopted']) + 1:03d}"
    feedback = experiment.worker_feedback(state, run_id)
    predecessor = (f"Property.candidates.v{len(state['runs'][run_id]['adopted']):03d}.Candidate"
                   if state["runs"][run_id]["adopted"] else "Property.Original")
    write_new(attempt_dir / "reformulator-start.json", {"role": "reformulator"})
    reform_inputs = role_inputs(root, chain)
    reform_inputs["grammar.md"] = root / "scripts/cedar/SYNTAX.md"
    reform = call_role("reformulator", root, attempt_dir, reform_inputs,
                       {"feedback": feedback, "predecessor": predecessor,
                        "candidate_syntax": "Inductive predicate : Original.Input -> Prop"},
                       chain, chains_root)
    write_new(attempt_dir / "reformulator-stage.json",
              {"status": reform["status"], "result": str(Path(reform["manifest"]["evidence"]) / "result.json")})
    if reform["status"] == "no_candidate":
        experiment.finish_attempt(state, run_id, attempt_id, status="no_candidate",
                                  reformulation_cost=_cost(reform), proof_cost=roles.not_run_cost(),
                                  reason=str((reform.get("answer") or {}).get("reason", ""))[:300])
        save_state(state_path, state)
        return
    if reform["status"] != "accepted" or (reform.get("answer") or {}).get("status") != "candidate":
        completed = reform.get("execution_status") == "completed"
        _finish_failure(state, run_id, attempt_id, reform, None,
                        "reformulator output rejected" if completed else "reformulator execution failed",
                        feedback_category="reformulator_output_rejected" if completed else "role_execution_failed")
        save_state(state_path, state)
        if completed:
            return
        if state["runs"][run_id]["stop_reason"] is None:
            experiment.stop_run(state, run_id, "operational_failure: reformulator")
        save_state(state_path, state)
        raise ExecutionError("reformulator role failed; run stopped with evidence")
    candidate = Path(reform["manifest"]["workspace"]) / "Candidate.v"
    summary = str(reform["answer"].get("summary", ""))[:300]
    frozen_candidate = digest(candidate)
    staged = _stage(chain, attempt_dir, version, candidate)
    write_new(attempt_dir / "candidate-stage.json",
              {"version": version, "candidate_sha256": frozen_candidate,
               "candidate": str(staged / "candidates" / version / "Candidate.v")})
    assert_frozen(root, frozen)
    syntax_ok, syntax_reason = syntax_check(root, staged, version, attempt_dir, frozen)
    write_new(attempt_dir / "syntax-stage.json",
              {"status": "passed" if syntax_ok else "failed", "result": str(attempt_dir / "syntax/result.json")})
    if not syntax_ok:
        _finish_failure(state, run_id, attempt_id, reform, None, syntax_reason, summary,
                        candidate, f"syntax_rejected: {syntax_reason[:200]}")
        save_state(state_path, state)
        return
    theorem = (f"forall x : Original.Input, {predecessor}.predicate x <-> "
               f"Property.candidates.{version}.Candidate.predicate x")
    write_new(attempt_dir / "prover-start.json", {"role": "prover",
                                                  "candidate_sha256": frozen_candidate})
    proof = call_role("prover", root, attempt_dir,
                      role_inputs(root, chain, candidate=staged / "candidates" / version / "Candidate.v", selected=version),
                      {"theorem_name": "equivalent", "theorem_type": theorem,
                       "frozen_candidate_sha256": frozen_candidate}, chain, chains_root)
    write_new(attempt_dir / "prover-stage.json",
              {"status": proof["status"], "result": str(Path(proof["manifest"]["evidence"]) / "result.json")})
    if digest(candidate) != frozen_candidate or digest(staged / "candidates" / version / "Candidate.v") != frozen_candidate:
        raise ExecutionError("prover stage changed frozen candidate")
    if proof["status"] != "accepted" or (proof.get("answer") or {}).get("status") != "proved":
        _finish_failure(state, run_id, attempt_id, reform, proof,
                        str((proof.get("answer") or {}).get("reason", "proof failed")),
                        summary, candidate, "proof_failed")
        save_state(state_path, state)
        return
    shutil.copyfile(Path(proof["manifest"]["workspace"]) / "Equivalence.v",
                    staged / "candidates" / version / "Equivalence.v")
    prefix_ok, prefix_reason = prefix_check(root, staged, attempt_dir, frozen)
    write_new(attempt_dir / "prefix-stage.json",
              {"status": "passed" if prefix_ok else "failed",
               "command_log": str(attempt_dir / "prefix-command.json")})
    if not prefix_ok:
        _finish_failure(state, run_id, attempt_id, reform, proof, prefix_reason,
                        summary, candidate, "prefix_failed")
        save_state(state_path, state)
        return
    assert_frozen(root, frozen)
    report = inspect_candidate(root, staged, chain, version, frozen_candidate,
                               frozen, attempt_dir)
    write_new(attempt_dir / "inspection-stage.json",
              {"status": report["status"],
               "result": str(attempt_dir / "inspection" / "result.json")})
    if report["status"] != "passed":
        _finish_failure(state, run_id, attempt_id, reform, proof,
                        "; ".join(report["violations"]) or "inspection failed",
                        summary, candidate, "inspection_failed")
        save_state(state_path, state)
        return
    try:
        inspection.check_candidate_report(attempt_dir / "inspection" / "result.json", version)
    except inspection.InspectionError as error:
        raise ExecutionError(str(error)) from error
    try:
        per_seed = measure(root, staged, version, experiment.EVAL_SEEDS, attempt_dir, frozen)
    except ProposalRejected as error:
        _finish_failure(state, run_id, attempt_id, reform, proof, str(error),
                        summary, candidate, "derivation_or_execution_failed")
        save_state(state_path, state)
        return
    if experiment.summarize_batches(per_seed, experiment.EVAL_SEEDS)["status"] != "completed":
        raise ExecutionError("incomplete candidate measurement cannot be adopted")
    write_new(attempt_dir / "measurement-stage.json",
              {"status": "completed", "candidate": version,
               "seeds": list(experiment.EVAL_SEEDS)})
    assert_frozen(root, frozen)
    if digest(staged / "candidates" / version / "Candidate.v") != frozen_candidate:
        raise ExecutionError("measured candidate differs from proved candidate")
    adopted = chain / "candidates" / version
    adopted.parent.mkdir(exist_ok=True)
    shutil.copytree(staged / "candidates" / version, adopted)
    experiment.finish_attempt(state, run_id, attempt_id, status="adopted",
                              reformulation_cost=_cost(reform), proof_cost=_cost(proof),
                              reason="verified", transformation_summary=summary,
                              candidate_sha256=frozen_candidate, per_seed=per_seed)
    save_state(state_path, state)


def run(experiment_id: str, review_path: Path, *, root: Path = ROOT,
        property_root: Path = PROPERTY) -> Path:
    if not SAFE_ID.fullmatch(experiment_id):
        raise ExecutionError("experiment id must use letters, numbers, underscore, hyphen")
    frozen = frozen_manifest(root)
    review_gate(review_path, frozen, property_root)
    evidence = property_root / ".runs" / experiment_id
    chains_root = property_root / "experiments" / experiment_id
    if evidence.exists() or chains_root.exists():
        raise ExecutionError("experiment id already exists; never resume or overwrite old sessions")
    evidence.mkdir(parents=True)
    chains_root.mkdir(parents=True)
    write_new(evidence / "manifest.json", {"frozen": frozen, "tool_review": str(review_path)})
    state = experiment.new_experiment(experiment_id, frozen["sources"], frozen["tools"])
    state_path = evidence / "state.json"
    save_state(state_path, state)
    for run_id in experiment.RUN_IDS:
        chain = chains_root / run_id
        chain.mkdir()
        shutil.copyfile(property_root / "Original.v", chain / "Original.v")
        if digest(chain / "Original.v") != frozen["sources"][SOURCE_FILES[1]]:
            raise ExecutionError("run Original differs from fixed source")
    baseline = evidence / "baseline-property"
    baseline.mkdir()
    shutil.copyfile(property_root / "Original.v", baseline / "Original.v")
    try:
        bridge = ensure_runtime_bridge(root)
        write_new(evidence / "runtime-bridge.json",
                  {"local": str(bridge), "installed": str(SWITCH.resolve(strict=True)),
                   "mode": "existing_pinned_switch_link"})
        version = checked_command(["bash", str(root / "environment/env.sh"), "coqc", "--version"],
                                  cwd=root, log=evidence / "environment-version.json", timeout=60)
        if (version.returncode != 0 or "version 8.20.0" not in version.stdout
                or "OCaml 4.14.2" not in version.stdout):
            raise ExecutionError("pinned Coq 8.20.0 / OCaml 4.14.2 environment unavailable")
        experiment.set_baseline(state, measure(root, baseline, "P0", experiment.EVAL_SEEDS,
                                               evidence / "baseline", frozen))
        save_state(state_path, state)
        for run_id in experiment.RUN_IDS:
            chain = chains_root / run_id
            while state["runs"][run_id]["stop_reason"] is None:
                execute_attempt(root, chain, chains_root, evidence, state, run_id, frozen, state_path)
            save_state(state_path, state)
        experiment.set_held_out_baseline(
            state, measure(root, baseline, "P0", experiment.HELD_OUT_SEEDS,
                           evidence / "held-out-baseline", frozen))
        save_state(state_path, state)
        for run_id in experiment.RUN_IDS:
            adopted = state["runs"][run_id]["adopted"]
            if not adopted:
                experiment.set_held_out_last(state, run_id, None)
            else:
                last = adopted[-1]["id"]
                experiment.set_held_out_last(
                    state, run_id, measure(root, chains_root / run_id, last,
                                           experiment.HELD_OUT_SEEDS,
                                           evidence / "held-out" / run_id, frozen))
            save_state(state_path, state)
        write_new(evidence / "summary.json", experiment.summary(state))
        write_new(evidence / "completion.json", {"status": "completed"})
    except Exception as error:
        stop_after_error(state, evidence, error)
        write_new(evidence / "operational-failure.json",
                  {"status": "stopped", "error_type": type(error).__name__, "error": str(error)})
        save_state(state_path, state)
        write_new(evidence / "summary.json", {"status": "stopped", **experiment.summary(state)})
        raise
    return evidence / "summary.json"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--experiment-id", required=True)
    parser.add_argument("--tool-review", required=True, type=Path)
    args = parser.parse_args()
    try:
        print(run(args.experiment_id, args.tool_review.resolve()))
    except (ExecutionError, experiment.ExperimentError, roles.RoleError, OSError,
            subprocess.SubprocessError, ValueError) as error:
        print(f"cedar execute: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
