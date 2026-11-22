#!/usr/bin/env python3
"""Re-measure an earlier Cedar experiment's P0 and adopted candidates.

No model role is called and no candidate is changed.  The adopted
``Candidate.v`` and ``Equivalence.v`` files of the source experiment are
verified against its ``final-audit.json`` hashes, staged, and measured through
the same ``execute.measure`` path as a new experiment: the five evaluation
seeds for P0 and every adopted candidate, and the five held-out seeds for P0
and each run's last adopted candidate.  A passed scripted tool review bound to
the current frozen manifest is required first.  Evidence is append-only under
``properties/cedar_no_type_error/.runs/EXPERIMENT_ID/`` and the summary under
``properties/cedar_no_type_error/experiments/EXPERIMENT_ID/``.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
from typing import Any, Callable, Mapping

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from scripts.cedar import execute, experiment

Measure = Callable[..., Mapping[int, Mapping[str, Any]]]


class RemeasureError(RuntimeError):
    pass


def _sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def adopted_chains(source: Path, audit: Mapping[str, Any]) -> dict[str, list[str]]:
    """Verify every adopted file against the source audit; return versions per run."""
    expected = {item["path"]: item["sha256"] for item in audit.get("adopted_artifacts", [])}
    if audit.get("status") != "passed" or not expected:
        raise RemeasureError("source experiment has no passed final audit")
    chains: dict[str, list[str]] = {}
    seen = set()
    for run_id in experiment.RUN_IDS:
        candidates = source / run_id / "candidates"
        versions = sorted(path.name for path in candidates.iterdir()) if candidates.is_dir() else []
        if versions != [f"v{index:03d}" for index in range(1, len(versions) + 1)]:
            raise RemeasureError(f"{run_id}: adopted versions are not contiguous: {versions}")
        for version in versions:
            for filename in ("Candidate.v", "Equivalence.v"):
                path = candidates / version / filename
                key = path.relative_to(execute.ROOT).as_posix()
                if expected.get(key) != _sha(path):
                    raise RemeasureError(f"adopted file differs from source audit: {key}")
                seen.add(key)
        chains[run_id] = versions
    if seen != set(expected):
        raise RemeasureError("source audit lists files outside the adopted chains")
    return chains


def stage_chain(source_chain: Path, staged: Path, original_sha: str) -> None:
    staged.mkdir(parents=True)
    shutil.copyfile(source_chain / "Original.v", staged / "Original.v")
    if _sha(staged / "Original.v") != original_sha:
        raise RemeasureError(f"{source_chain}: Original.v differs from the frozen source")
    if (source_chain / "candidates").is_dir():
        shutil.copytree(source_chain / "candidates", staged / "candidates")


def summarize(state: Mapping[str, Any]) -> dict[str, Any]:
    baseline = state["baseline"]
    held_baseline = state["held_out_baseline"]
    runs = {}
    for run_id, run in state["runs"].items():
        adopted, previous = [], baseline
        for item in run["adopted"]:
            measurement = item["measurement"]
            adopted.append({**item, "comparison": {
                "vs_P0": experiment._difference(measurement, baseline),
                "vs_predecessor": experiment._difference(measurement, previous)}})
            previous = measurement
        held = run.get("held_out")
        if held is not None:
            held = {**held, "comparison": experiment._difference(held["measurement"], held_baseline)}
        runs[run_id] = {"adopted": adopted, "held_out": held,
                        "last_candidate_id": adopted[-1]["id"] if adopted else None}
    return {"experiment_id": state["experiment_id"], "source_experiment": state["source_experiment"],
            "baseline": baseline, "held_out_baseline": held_baseline, "runs": runs}


def remeasure(source_id: str, experiment_id: str, review_path: Path, *,
              root: Path = execute.ROOT, property_root: Path = execute.PROPERTY,
              measure: Measure = execute.measure) -> Path:
    if not execute.SAFE_ID.fullmatch(experiment_id) or not execute.SAFE_ID.fullmatch(source_id):
        raise RemeasureError("experiment ids must use letters, numbers, underscore, hyphen")
    frozen = execute.frozen_manifest(root)
    execute.review_gate(review_path, frozen, property_root)
    source = property_root / "experiments" / source_id
    audit = json.loads((source / "final-audit.json").read_text())
    chains = adopted_chains(source, audit)
    evidence = property_root / ".runs" / experiment_id
    results = property_root / "experiments" / experiment_id
    if evidence.exists() or results.exists():
        raise RemeasureError("experiment id already exists; evidence is append-only")
    evidence.mkdir(parents=True)
    results.mkdir(parents=True)
    original_sha = frozen["sources"][execute.SOURCE_FILES[1]]
    manifest = {"frozen": frozen, "tool_review": str(review_path), "source_experiment": source_id,
                "source_final_audit_sha256": _sha(source / "final-audit.json"),
                "chains": chains}
    execute.write_new(evidence / "manifest.json", manifest)
    execute.write_new(results / "manifest.json", manifest)
    state: dict[str, Any] = {"experiment_id": experiment_id, "source_experiment": source_id,
                             "baseline": None, "held_out_baseline": None,
                             "runs": {run_id: {"adopted": [], "held_out": None}
                                      for run_id in chains}}
    state_path = evidence / "state.json"
    execute.save_state(state_path, state)

    def measured(staged: Path, candidate: str, seeds: tuple[int, ...], where: Path) -> dict:
        execute.assert_frozen(root, frozen)
        result = experiment.summarize_batches(measure(root, staged, candidate, seeds, where, frozen),
                                              seeds)
        if result["status"] != "completed":
            raise RemeasureError(f"incomplete measurement for {candidate} at {where}")
        return result

    try:
        execute.ensure_runtime_bridge(root)
        baseline = evidence / "baseline-property"
        baseline.mkdir()
        shutil.copyfile(property_root / "Original.v", baseline / "Original.v")
        state["baseline"] = measured(baseline, "P0", experiment.EVAL_SEEDS, evidence / "baseline")
        execute.save_state(state_path, state)
        state["held_out_baseline"] = measured(baseline, "P0", experiment.HELD_OUT_SEEDS,
                                              evidence / "held-out-baseline")
        execute.save_state(state_path, state)
        for run_id, versions in chains.items():
            staged = evidence / run_id / "staged-property"
            stage_chain(source / run_id, staged, original_sha)
            for version in versions:
                sha = _sha(staged / "candidates" / version / "Candidate.v")
                result = measured(staged, version, experiment.EVAL_SEEDS,
                                  evidence / run_id / version)
                state["runs"][run_id]["adopted"].append(
                    {"id": version, "candidate_sha256": sha, "measurement": result})
                execute.save_state(state_path, state)
            if versions:
                last = versions[-1]
                state["runs"][run_id]["held_out"] = {
                    "candidate": last,
                    "measurement": measured(staged, last, experiment.HELD_OUT_SEEDS,
                                            evidence / "held-out" / run_id)}
                execute.save_state(state_path, state)
        summary = summarize(state)
        execute.write_new(evidence / "summary.json", summary)
        execute.write_new(results / "summary.json", summary)
        execute.write_new(evidence / "completion.json", {"status": "completed"})
    except Exception as error:
        execute.write_new(evidence / "operational-failure.json",
                          {"status": "stopped", "error_type": type(error).__name__,
                           "error": str(error)})
        execute.save_state(state_path, state)
        raise
    return results / "summary.json"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--source", required=True, help="earlier experiment id")
    parser.add_argument("--experiment-id", required=True)
    parser.add_argument("--tool-review", required=True, type=Path)
    args = parser.parse_args()
    try:
        print(remeasure(args.source, args.experiment_id, args.tool_review.resolve()))
    except (RemeasureError, execute.ExecutionError, experiment.ExperimentError,
            OSError, ValueError) as error:
        print(f"cedar remeasure: {error}", file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
