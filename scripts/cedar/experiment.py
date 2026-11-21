"""Pure bookkeeping for the fixed three-run Cedar experiment.

This module records externally supplied benchmark counts and role costs.  It
does not execute roles, validate generated values, or claim a Coq proof.
"""

from __future__ import annotations

from copy import deepcopy
from typing import Any, Mapping


EVAL_SEEDS = (101, 202, 303, 404, 505)
HELD_OUT_SEEDS = (1101, 1202, 1303, 1404, 1505)
RUN_IDS = ("run-001", "run-002", "run-003")
SIZE = 2
ATTEMPTS_PER_SEED = 10000
MAX_PROPOSALS = 10
COUNT_KEYS = ("confirmed_valid", "confirmed_invalid", "no_result", "undetermined")


class ExperimentError(ValueError):
    pass


def _run(state: dict[str, Any], run_id: str) -> dict[str, Any]:
    if run_id not in state["runs"]:
        raise ExperimentError(f"Unknown run: {run_id}")
    return state["runs"][run_id]


def new_experiment(experiment_id: str, source_hashes: Mapping[str, str],
                   tool_hashes: Mapping[str, str], *,
                   eval_seeds: tuple[int, ...] = EVAL_SEEDS,
                   held_out_seeds: tuple[int, ...] = HELD_OUT_SEEDS) -> dict[str, Any]:
    if len(eval_seeds) != 5 or len(held_out_seeds) != 5 or len(set(eval_seeds + held_out_seeds)) != 10:
        raise ExperimentError("Five distinct evaluation and held-out seeds are required")
    if not experiment_id or not source_hashes or not tool_hashes:
        raise ExperimentError("Experiment ID and frozen source/tool hashes are required")
    return {"experiment_id": experiment_id,
            "frozen_hashes": {"sources": dict(source_hashes), "tools": dict(tool_hashes)},
            "conditions": {"size": SIZE, "attempts_per_seed": ATTEMPTS_PER_SEED,
                           "eval_seeds": list(eval_seeds), "held_out_seeds": list(held_out_seeds),
                           "max_proposals_per_run": MAX_PROPOSALS},
            "baseline": None, "held_out_baseline": None,
            "runs": {run_id: {"attempts": [], "adopted": [], "stop_reason": None,
                              "held_out": None} for run_id in RUN_IDS}}


def summarize_batches(per_seed: Mapping[int, Mapping[str, Any]],
                      seeds: tuple[int, ...]) -> dict[str, Any]:
    if set(per_seed) != set(seeds):
        raise ExperimentError("Batch seed set differs from frozen conditions")
    summaries = {}
    totals = {key: 0 for key in COUNT_KEYS}
    total_attempts = 0
    complete = True
    for seed in seeds:
        batch = per_seed[seed]
        if not all(type(batch.get(key)) is int and batch[key] >= 0 for key in COUNT_KEYS):
            raise ExperimentError(f"Missing or invalid raw count for seed {seed}")
        attempts = batch.get("attempts")
        if type(attempts) is not int or attempts < 0 or attempts > ATTEMPTS_PER_SEED:
            raise ExperimentError(f"Invalid external attempt count for seed {seed}")
        if sum(batch[key] for key in COUNT_KEYS) != attempts:
            raise ExperimentError(f"Raw counts do not partition attempts for seed {seed}")
        status = batch.get("status")
        if status not in ("completed", "incomplete"):
            raise ExperimentError(f"Missing batch status for seed {seed}")
        if status == "completed" and attempts != ATTEMPTS_PER_SEED:
            raise ExperimentError(f"Completed batch has fewer than 10000 attempts for seed {seed}")
        is_complete = status == "completed"
        complete &= is_complete
        for key in COUNT_KEYS:
            totals[key] += batch[key]
        total_attempts += attempts
        summaries[str(seed)] = {"status": status, "attempts": attempts,
                                **{key: batch[key] for key in COUNT_KEYS},
                                "confirmed_valid_ratio": (batch["confirmed_valid"] / attempts
                                                          if is_complete else None)}
    return {"status": "completed" if complete else "incomplete",
            "per_seed": summaries, "totals": {"attempts": total_attempts, **totals},
            "confirmed_valid_ratio": (totals["confirmed_valid"] / total_attempts
                                      if complete and total_attempts else None)}


def set_baseline(state: dict[str, Any], per_seed: Mapping[int, Mapping[str, Any]]) -> None:
    if state["baseline"] is not None:
        raise ExperimentError("P0 baseline is immutable")
    if any(run["attempts"] for run in state["runs"].values()):
        raise ExperimentError("P0 baseline must be measured before proposals")
    seeds = tuple(state["conditions"]["eval_seeds"])
    baseline = summarize_batches(per_seed, seeds)
    if baseline["status"] != "completed":
        raise ExperimentError("Incomplete P0 baseline cannot start exploration")
    state["baseline"] = baseline


def begin_attempt(state: dict[str, Any], run_id: str) -> str:
    run = _run(state, run_id)
    if state["baseline"] is None:
        raise ExperimentError("Measure P0 before starting a role")
    if run["stop_reason"] is not None:
        raise ExperimentError(f"Run already stopped: {run_id}")
    if any(attempt["status"] == "pending" for attempt in run["attempts"]):
        raise ExperimentError("Finish the current proposal before starting another")
    if len(run["attempts"]) >= MAX_PROPOSALS:
        raise ExperimentError("Ten-proposal limit reached")
    attempt_id = f"attempt-{len(run['attempts']) + 1:03d}"
    run["attempts"].append({"id": attempt_id, "status": "pending", "adopted_id": None,
                            "reformulation_cost": None, "proof_cost": None,
                            "reason": None, "feedback_summary": None,
                            "transformation_summary": None,
                            "measurement": None, "candidate_sha256": None})
    return attempt_id


def finish_attempt(state: dict[str, Any], run_id: str, attempt_id: str, *,
                   status: str, reformulation_cost: Mapping[str, Any],
                   proof_cost: Mapping[str, Any], reason: str = "",
                   feedback_summary: str = "", transformation_summary: str = "",
                   candidate_sha256: str | None = None,
                   per_seed: Mapping[int, Mapping[str, Any]] | None = None) -> dict[str, Any]:
    run = _run(state, run_id)
    if not run["attempts"] or run["attempts"][-1]["id"] != attempt_id:
        raise ExperimentError("Only the current proposal may be finished")
    attempt = run["attempts"][-1]
    if attempt["status"] != "pending" or status not in ("adopted", "rejected", "no_candidate"):
        raise ExperimentError("Invalid proposal transition")
    if not isinstance(reformulation_cost, Mapping) or not isinstance(proof_cost, Mapping):
        raise ExperimentError("Both role costs or explicit not_run values are required")
    if status == "adopted":
        if not candidate_sha256 or per_seed is None:
            raise ExperimentError("Adoption needs candidate hash and completed measurement")
        measurement = summarize_batches(per_seed, tuple(state["conditions"]["eval_seeds"]))
        if measurement["status"] != "completed":
            raise ExperimentError("Incomplete measurement cannot be adopted")
        predecessor = run["adopted"][-1]["measurement"] if run["adopted"] else state["baseline"]
        adopted_id = f"v{len(run['adopted']) + 1:03d}"
        comparison = {"vs_P0": _difference(measurement, state["baseline"]),
                      "vs_predecessor": _difference(measurement, predecessor)}
        record = {"id": adopted_id, "from_attempt": attempt_id,
                  "candidate_sha256": candidate_sha256, "measurement": measurement,
                  "comparison": comparison}
        run["adopted"].append(record)
        attempt.update(status=status, adopted_id=adopted_id,
                       measurement=measurement, candidate_sha256=candidate_sha256)
    else:
        if per_seed is not None or candidate_sha256 is not None and status == "no_candidate":
            raise ExperimentError("Failed/no_candidate proposal cannot carry adopted measurement")
        attempt["status"] = status
        attempt["candidate_sha256"] = candidate_sha256
        if status == "no_candidate":
            run["stop_reason"] = "no_candidate"
    attempt["reformulation_cost"] = deepcopy(dict(reformulation_cost))
    attempt["proof_cost"] = deepcopy(dict(proof_cost))
    attempt["reason"] = reason
    attempt["feedback_summary"] = feedback_summary[:300]
    attempt["transformation_summary"] = transformation_summary[:300]
    if len(run["attempts"]) == MAX_PROPOSALS and run["stop_reason"] is None:
        run["stop_reason"] = "attempt_limit"
    return attempt


def _difference(candidate: Mapping[str, Any], reference: Mapping[str, Any]) -> dict[str, Any]:
    candidate_ratio = candidate["confirmed_valid_ratio"]
    reference_ratio = reference["confirmed_valid_ratio"]
    per_seed = {}
    for seed, candidate_batch in candidate["per_seed"].items():
        reference_batch = reference["per_seed"][seed]
        c = candidate_batch["confirmed_valid_ratio"]
        r = reference_batch["confirmed_valid_ratio"]
        per_seed[seed] = {"candidate_ratio": c, "reference_ratio": r,
                          "difference": c - r if c is not None and r is not None else None}
    return {"candidate_ratio": candidate_ratio, "reference_ratio": reference_ratio,
            "difference": (candidate_ratio - reference_ratio
                           if candidate_ratio is not None and reference_ratio is not None else None),
            "per_seed": per_seed}


def stop_run(state: dict[str, Any], run_id: str, reason: str) -> None:
    run = _run(state, run_id)
    if any(attempt["status"] == "pending" for attempt in run["attempts"]):
        raise ExperimentError("Cannot stop with a pending proposal")
    if run["stop_reason"] is not None:
        raise ExperimentError("Stop reason already fixed")
    if not reason:
        raise ExperimentError("Concrete stop reason required")
    run["stop_reason"] = reason


def worker_feedback(state: Mapping[str, Any], run_id: str) -> dict[str, Any]:
    """Only this run's numeric evaluation and brief failed-attempt feedback."""
    run = state["runs"][run_id]
    last = run["adopted"][-1] if run["adopted"] else None
    return {"baseline": deepcopy(state["baseline"]),
            "predecessor": deepcopy(last["measurement"]) if last else None,
            "attempts": [{"id": item["id"], "status": item["status"],
                          "transformation_summary": item["transformation_summary"],
                          "feedback_summary": item["feedback_summary"]}
                         for item in run["attempts"]]}


def set_held_out_baseline(state: dict[str, Any], per_seed: Mapping[int, Mapping[str, Any]]) -> None:
    if state["held_out_baseline"] is not None:
        raise ExperimentError("Held-out P0 result is immutable")
    if any(run["stop_reason"] is None for run in state["runs"].values()):
        raise ExperimentError("Finish all exploration runs before held-out evaluation")
    state["held_out_baseline"] = summarize_batches(per_seed, tuple(state["conditions"]["held_out_seeds"]))


def set_held_out_last(state: dict[str, Any], run_id: str,
                      per_seed: Mapping[int, Mapping[str, Any]] | None) -> None:
    run = _run(state, run_id)
    if state["held_out_baseline"] is None or run["held_out"] is not None:
        raise ExperimentError("Held-out baseline must be fixed first; result is immutable")
    if not run["adopted"]:
        if per_seed is not None:
            raise ExperimentError("Run with no adopted candidate has no last candidate to reevaluate")
        run["held_out"] = {"status": "no_adopted_candidate"}
        return
    if per_seed is None:
        raise ExperimentError("Missing final candidate reevaluation")
    result = summarize_batches(per_seed, tuple(state["conditions"]["held_out_seeds"]))
    run["held_out"] = {"status": result["status"], "candidate": run["adopted"][-1]["id"],
                       "measurement": result,
                       "comparison": (_difference(result, state["held_out_baseline"])
                                      if result["status"] == "completed"
                                      and state["held_out_baseline"]["status"] == "completed" else None)}


def summary(state: Mapping[str, Any]) -> dict[str, Any]:
    """Report only requested comparison, role-cost, and stop information."""
    def summarize_run(run: Mapping[str, Any]) -> dict[str, Any]:
        adopted = run["adopted"]
        last = adopted[-1] if adopted else None
        # First accepted candidate wins a tie, so this is deterministic.
        best = max(adopted, key=lambda item: item["measurement"]["confirmed_valid_ratio"],
                   default=None)
        return {"proposal_count": len(run["attempts"]),
                "adopted_count": len(adopted), "stop_reason": run["stop_reason"],
                "last_candidate_id": last["id"] if last else None,
                "best_candidate_id": best["id"] if best else None,
                "best_confirmed_valid_ratio": (best["measurement"]["confirmed_valid_ratio"]
                                               if best else None),
                "attempts": deepcopy(run["attempts"]), "adopted": deepcopy(adopted),
                "held_out": deepcopy(run["held_out"])}
    return {"experiment_id": state["experiment_id"], "baseline": deepcopy(state["baseline"]),
            "held_out_baseline": deepcopy(state["held_out_baseline"]),
            "runs": {name: summarize_run(run)
                     for name, run in state["runs"].items()}}
