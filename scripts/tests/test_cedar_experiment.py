"""Pure experiment bookkeeping regressions; no model or benchmark invocation."""

import unittest

from scripts.cedar import experiment as e


def batches(seeds, valid, *, incomplete_seed=None):
    result = {}
    for seed in seeds:
        attempts = 120 if seed == incomplete_seed else e.ATTEMPTS_PER_SEED
        count = min(valid, attempts - 1)
        result[seed] = {"status": "incomplete" if seed == incomplete_seed else "completed",
                        "attempts": attempts, "confirmed_valid": count,
                        "confirmed_invalid": attempts - count - 1,
                        "no_result": 1, "undetermined": 0}
    return result


class ExperimentTests(unittest.TestCase):
    def setUp(self):
        self.state = e.new_experiment("test", {"Spec.v": "a", "Original.v": "b"},
                                      {"benchmark.py": "c", "roles.py": "d"})
        e.set_baseline(self.state, batches(e.EVAL_SEEDS, 500))

    def test_failed_proposal_counts_and_next_adopted_number_is_v001(self):
        first = e.begin_attempt(self.state, "run-001")
        self.assertEqual(first, "attempt-001")
        e.finish_attempt(self.state, "run-001", first, status="rejected",
                         reformulation_cost={"wall_seconds": 7, "usage": {"input_tokens": 30}},
                         proof_cost={"status": "not_run"}, reason="shape failed",
                         candidate_sha256="candidate-a", transformation_summary="split constructor")
        second = e.begin_attempt(self.state, "run-001")
        self.assertEqual(second, "attempt-002")
        adopted = e.finish_attempt(self.state, "run-001", second, status="adopted",
                                   reformulation_cost={"wall_seconds": 8},
                                   proof_cost={"wall_seconds": 9},
                                   candidate_sha256="candidate-b",
                                   per_seed=batches(e.EVAL_SEEDS, 400))
        self.assertEqual(adopted["adopted_id"], "v001")
        self.assertAlmostEqual(self.state["runs"]["run-001"]["adopted"][0]["comparison"]["vs_P0"]["difference"], -0.01)
        self.assertEqual(len(self.state["runs"]["run-001"]["attempts"]), 2)

    def test_no_candidate_ends_run_and_preserves_not_run_proof(self):
        attempt = e.begin_attempt(self.state, "run-002")
        e.finish_attempt(self.state, "run-002", attempt, status="no_candidate",
                         reformulation_cost={"wall_seconds": 2},
                         proof_cost={"status": "not_run"}, reason="none found")
        self.assertEqual(self.state["runs"]["run-002"]["stop_reason"], "no_candidate")
        self.assertEqual(self.state["runs"]["run-002"]["attempts"][0]["proof_cost"]["status"], "not_run")
        with self.assertRaises(e.ExperimentError):
            e.begin_attempt(self.state, "run-002")

    def test_ten_attempt_limit_includes_failures(self):
        for n in range(10):
            attempt = e.begin_attempt(self.state, "run-003")
            e.finish_attempt(self.state, "run-003", attempt, status="rejected",
                             reformulation_cost={"wall_seconds": 1},
                             proof_cost={"status": "not_run"}, reason="rejected")
        self.assertEqual(self.state["runs"]["run-003"]["stop_reason"], "attempt_limit")
        with self.assertRaises(e.ExperimentError):
            e.begin_attempt(self.state, "run-003")

    def test_incomplete_batch_keeps_raw_counts_and_has_no_ratio(self):
        result = e.summarize_batches(batches(e.EVAL_SEEDS, 500, incomplete_seed=202), e.EVAL_SEEDS)
        self.assertEqual(result["status"], "incomplete")
        self.assertEqual(result["totals"]["attempts"], 40120)
        self.assertIsNone(result["confirmed_valid_ratio"])
        self.assertEqual(result["per_seed"]["202"]["attempts"], 120)
        attempt = e.begin_attempt(self.state, "run-001")
        with self.assertRaises(e.ExperimentError):
            e.finish_attempt(self.state, "run-001", attempt, status="adopted",
                             reformulation_cost={}, proof_cost={},
                             candidate_sha256="x", per_seed=batches(e.EVAL_SEEDS, 500, incomplete_seed=202))

    def test_held_out_phase_is_separate_from_worker_feedback(self):
        for run_id in e.RUN_IDS:
            e.stop_run(self.state, run_id, "operational stop")
        e.set_held_out_baseline(self.state, batches(e.HELD_OUT_SEEDS, 600))
        for run_id in e.RUN_IDS:
            e.set_held_out_last(self.state, run_id, None)
        feedback = e.worker_feedback(self.state, "run-001")
        self.assertNotIn("held_out", str(feedback))
        self.assertEqual(feedback["attempts"], [])
        self.assertEqual(e.summary(self.state)["runs"]["run-001"]["held_out"]["status"],
                         "no_adopted_candidate")

    def test_last_adopted_remains_distinct_from_best_when_later_is_worse(self):
        for n, valid in enumerate((700, 400, 700), start=1):
            attempt = e.begin_attempt(self.state, "run-001")
            e.finish_attempt(self.state, "run-001", attempt, status="adopted",
                             reformulation_cost={"wall_seconds": n},
                             proof_cost={"wall_seconds": n},
                             candidate_sha256=f"candidate-{n}",
                             per_seed=batches(e.EVAL_SEEDS, valid))
        report = e.summary(self.state)["runs"]["run-001"]
        self.assertEqual(report["last_candidate_id"], "v003")
        self.assertEqual(report["best_candidate_id"], "v001")
        self.assertEqual(report["best_confirmed_valid_ratio"], 0.07)
        self.assertEqual(report["adopted_count"], 3)

    def test_mismatched_seed_or_unpartitioned_counts_fail(self):
        with self.assertRaises(e.ExperimentError):
            e.summarize_batches({101: batches((101,), 1)[101]}, e.EVAL_SEEDS)
        broken = batches(e.EVAL_SEEDS, 500)
        broken[101]["no_result"] += 1
        with self.assertRaises(e.ExperimentError):
            e.summarize_batches(broken, e.EVAL_SEEDS)


if __name__ == "__main__":
    unittest.main()
