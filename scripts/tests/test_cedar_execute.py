"""Coordinator boundary regressions; no model, Coq, benchmark, or validator calls."""

import json
import threading
from pathlib import Path
import sys
import tempfile
from types import SimpleNamespace
import time
import unittest
from unittest import mock

from scripts.cedar import execute, experiment, roles


def batches(seeds, valid=1, *, status="completed"):
    count = experiment.ATTEMPTS_PER_SEED if status == "completed" else 3
    return {seed: {"status": status, "attempts": count,
                   "confirmed_valid": min(valid, count),
                   "confirmed_invalid": count - min(valid, count),
                   "no_result": 0, "undetermined": 0} for seed in seeds}


class ReviewGateTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="cedar-execute-review-")
        self.addCleanup(self.temp.cleanup)
        self.prop = Path(self.temp.name) / "property"
        self.private = self.prop / ".runs"
        self.workspace = self.private / "review-role/workspace"
        self.evidence = self.private / "review-role/private-evidence"
        (self.workspace / "scratch").mkdir(parents=True)
        self.evidence.mkdir()
        (self.workspace / "scratch/checked.log").write_text("passed\n")
        (self.evidence / "events.jsonl").write_text('{"type":"turn.completed"}\n')
        (self.workspace / "Spec.v").write_text("source\n")
        (self.workspace / "benchmark.py").write_text("tool\n")
        prompt = "scripts/cedar/prompts/inspector.txt"
        schema = "scripts/cedar/schemas/inspector.json"
        for name in (prompt, schema):
            target = self.workspace / name
            target.parent.mkdir(parents=True)
            target.write_bytes((execute.ROOT / name).read_bytes())
        self.frozen = {"commit": "a" * 40,
                       "sources": {"Spec.v": execute.digest(self.workspace / "Spec.v")},
                       "tools": {"benchmark.py": execute.digest(self.workspace / "benchmark.py"),
                                 prompt: execute.digest(self.workspace / prompt),
                                 schema: execute.digest(self.workspace / schema)},
                       "conditions": {"size": 2}}
        context = {"frozen": self.frozen, "purpose": "independent_tool_review"}
        (self.workspace / "context.json").write_text(json.dumps(context))
        self.report = {"status": "accepted", "execution_status": "completed",
                       "manifest": {"role": "inspector", "model": roles.MODEL,
                                    "effort": roles.EFFORT["inspector"],
                                    "workspace": str(self.workspace),
                                    "evidence": str(self.evidence),
                                    "input_sha256": {**self.frozen["sources"], **self.frozen["tools"]},
                                    "context_sha256": execute.digest(self.workspace / "context.json"),
                                    "prompt_sha256": self.frozen["tools"][prompt],
                                    "schema_sha256": self.frozen["tools"][schema]},
                       "changed_source_files": [],
                       "sandbox": {"kind": "Landlock",
                                   "probe": str(self.evidence / "sandbox-probe.json")},
                       "answer": {"status": "passed", "commands": ["python3 -m unittest"],
                                  "evidence_paths": ["scratch/checked.log"], "violations": []}}
        (self.evidence / "sandbox-probe.json").write_text('{"status":"passed"}\n')
        self.result = self.evidence / "result.json"
        self.result.write_text(json.dumps(self.report))
        self.review = self.private / "tool-review.json"
        self.review.write_text(json.dumps({"frozen": self.frozen,
                                           "inspector_result": str(self.result)}))

    def test_exact_inspector_evidence_passes(self):
        self.assertEqual(execute.review_gate(self.review, self.frozen, self.prop)["frozen"],
                         self.frozen)

    def test_review_rejects_changed_hash_and_unaccepted_inspector(self):
        wrong = {**self.frozen, "tools": {"benchmark.py": "different"}}
        with self.assertRaises(execute.ExecutionError):
            execute.review_gate(self.review, wrong, self.prop)
        self.report["status"] = "rejected"
        self.result.write_text(json.dumps(self.report))
        with self.assertRaises(execute.ExecutionError):
            execute.review_gate(self.review, self.frozen, self.prop)

    def test_review_rejects_missing_or_external_inspector_logs(self):
        (self.workspace / "scratch/checked.log").unlink()
        with self.assertRaises(execute.ExecutionError):
            execute.review_gate(self.review, self.frozen, self.prop)
        self.report["answer"]["evidence_paths"] = ["/etc/passwd"]
        self.result.write_text(json.dumps(self.report))
        with self.assertRaises(execute.ExecutionError):
            execute.review_gate(self.review, self.frozen, self.prop)

    def test_run_requires_review_before_creating_evidence_or_calling_benchmark(self):
        with mock.patch.object(execute, "frozen_manifest", return_value=self.frozen), \
             mock.patch.object(execute, "measure", side_effect=AssertionError("benchmark called")):
            with self.assertRaises(execute.ExecutionError):
                execute.run("new-experiment", self.private / "absent.json",
                            root=Path(self.temp.name), property_root=self.prop)
        self.assertFalse((self.private / "new-experiment").exists())
        self.assertFalse((self.prop / "experiments/new-experiment").exists())


class OrchestrationTests(unittest.TestCase):
    def test_measure_runs_seeds_concurrently_and_keeps_seed_evidence(self):
        seeds = (101, 202, 303)
        barrier = threading.Barrier(len(seeds))
        with tempfile.TemporaryDirectory(prefix="cedar-measure-") as directory:
            root = Path(directory)
            staged = root / "property"
            evidence = root / "evidence"
            evidence.mkdir()

            def completed(_root, _staged, candidate, seed, _evidence, _frozen):
                self.assertEqual(candidate, "P0")
                barrier.wait(timeout=5)
                return batches((seed,), valid=seed // 101)[seed]

            with mock.patch.object(execute, "benchmark_batch", side_effect=completed):
                result = execute.measure(root, staged, "P0", seeds, evidence, {})
            self.assertEqual(list(result), list(seeds))
            self.assertEqual(result, batches((101,), valid=1) |
                             batches((202,), valid=2) | batches((303,), valid=3))
            for seed in seeds:
                record = json.loads((evidence / f"batch-P0-{seed}.json").read_text())
                self.assertEqual(record["seed"], seed)
                self.assertEqual(record["counts"], result[seed])
                self.assertEqual(record["benchmark_result"],
                                 str(staged / ".runs" / f"benchmark-P0-{seed}" / "result.json"))

    def test_measure_failure_waits_for_other_seed_evidence_without_returning(self):
        seeds = (101, 202, 303)
        barrier = threading.Barrier(len(seeds))
        with tempfile.TemporaryDirectory(prefix="cedar-measure-failure-") as directory:
            root = Path(directory)
            evidence = root / "evidence"
            evidence.mkdir()

            def partially_completed(_root, _staged, _candidate, seed, _evidence, _frozen):
                barrier.wait(timeout=5)
                if seed == 202:
                    raise execute.ExecutionError("seed 202 failed")
                return batches((seed,))[seed]

            with mock.patch.object(execute, "benchmark_batch", side_effect=partially_completed):
                with self.assertRaisesRegex(execute.ExecutionError, "seed 202 failed"):
                    execute.measure(root, root / "property", "P0", seeds, evidence, {})
            for seed in (101, 303):
                self.assertEqual(json.loads((evidence / f"batch-P0-{seed}.json").read_text())["seed"],
                                 seed)
            self.assertFalse((evidence / "batch-P0-202.json").exists())

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="cedar-execute-attempt-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "source"
        self.chain_root = self.root / "properties/property/experiments/test"
        self.chain = self.chain_root / "run-001"
        self.chain.mkdir(parents=True)
        (self.root / "specification/cedar").mkdir(parents=True)
        (self.root / "specification/cedar/Spec.v").write_text("(* fixed *)\n")
        (self.chain / "Original.v").write_text("(* original *)\n")
        for name in execute.SOURCE_FILES + execute.TOOL_FILES:
            path = self.root / name
            path.parent.mkdir(parents=True, exist_ok=True)
            if not path.exists():
                path.write_text("fixture\n")
        (self.root / "scripts/cedar/SYNTAX.md").write_text("fixed grammar\n")
        self.evidence = self.root / "properties/property/.runs/test"
        self.evidence.mkdir(parents=True)
        self.state = experiment.new_experiment("test", {"s": "s"}, {"t": "t"})
        experiment.set_baseline(self.state, batches(experiment.EVAL_SEEDS))
        self.state_path = self.evidence / "state.json"
        execute.save_state(self.state_path, self.state)
        self.frozen = {"conditions": {}, "sources": {}, "tools": {}}

    def _role(self, role, root, attempt_dir, inputs, context, own_run, chains_root):
        self.assertEqual(own_run, self.chain)
        self.assertNotIn("held_out", json.dumps(context))
        self.assertNotIn("run-002", json.dumps(context))
        if role != "inspector":
            self.assertFalse(any("Equivalence.v" in name for name in inputs))
            self.assertFalse(any("benchmark.py" in name for name in inputs))
        if role == "reformulator":
            self.assertEqual(inputs["grammar.md"], self.root / "scripts/cedar/SYNTAX.md")
        if role == "prover":
            self.assertNotIn("grammar.md", inputs)
        workspace = attempt_dir / f"fake-{role}"
        workspace.mkdir()
        if role == "reformulator":
            (workspace / "Candidate.v").write_text("Inductive predicate : nat -> Prop := c : predicate 0.\n")
            answer = {"status": "candidate", "summary": "constructor split"}
        elif role == "prover":
            self.assertEqual(context["theorem_type"],
                             "forall x : Original.Input, Property.Original.predicate x <-> "
                             "Property.candidates.v001.Candidate.predicate x")
            self.assertEqual(context["frozen_candidate_sha256"], execute.digest(inputs["Candidate.v"]))
            (workspace / "Equivalence.v").write_text("Theorem equivalent : True. Proof. exact I. Qed.\n")
            answer = {"status": "proved", "reason": ""}
        else:
            self.assertIn("property/candidates/v001/Equivalence.v", inputs)
            self.assertEqual(context["purpose"], "candidate_inspection")
            answer = {"status": "passed", "commands": ["coqchk"],
                      "evidence_paths": ["scratch/check.log"], "violations": []}
        private = attempt_dir / "roles" / f"{role}-fake" / "private-evidence"
        private.mkdir(parents=True)
        (private / "result.json").write_text("{}")
        return {"status": "accepted", "answer": answer,
                "manifest": {"workspace": str(workspace), "evidence": str(private)},
                "cost": {"status": "measured", "wall_seconds": 5,
                         "usage": {"status": "available", "input_tokens": 10,
                                   "output_tokens": 2}}}

    def _run(self, **patches):
        defaults = {"assert_frozen": lambda *args: None,
                    "call_role": self._role,
                    "syntax_check": lambda *args: (True, ""),
                    "prefix_check": lambda *args: (True, ""),
                    "inspect_result": lambda *args: {},
                    "measure": lambda *args: batches(experiment.EVAL_SEEDS)}
        defaults.update(patches)
        with mock.patch.multiple(execute, **defaults):
            execute.execute_attempt(self.root, self.chain, self.chain_root,
                                    self.evidence, self.state, "run-001",
                                    self.frozen, self.state_path)

    def test_rejected_syntax_stays_private_and_prover_cost_not_run(self):
        def no_prover(role, *args):
            self.assertEqual(role, "reformulator")
            return self._role(role, *args)
        self._run(syntax_check=lambda *args: (False, "shape invalid"), call_role=no_prover)
        attempt = self.state["runs"]["run-001"]["attempts"][0]
        self.assertEqual(attempt["status"], "rejected")
        self.assertEqual(attempt["proof_cost"]["status"], "not_run")
        self.assertFalse((self.chain / "candidates/v001").exists())
        self.assertTrue((self.evidence / "run-001/attempt-001/staged-property/candidates/v001/Candidate.v").exists())

    def test_completed_reformulator_scope_rejection_counts_and_continues(self):
        def rejected(role, *args):
            self.assertEqual(role, "reformulator")
            report = self._role(role, *args)
            report.update(status="rejected", execution_status="completed")
            return report
        self._run(call_role=rejected,
                  syntax_check=lambda *args: self.fail("rejected output must not enter syntax"))
        run = self.state["runs"]["run-001"]
        self.assertEqual(run["attempts"][0]["status"], "rejected")
        self.assertEqual(run["attempts"][0]["reformulation_cost"]["wall_seconds"], 5)
        self.assertEqual(run["attempts"][0]["proof_cost"]["status"], "not_run")
        self.assertIsNone(run["stop_reason"])
        self.assertEqual(experiment.begin_attempt(self.state, "run-001"), "attempt-002")

    def test_failed_prefix_cannot_adopt_even_after_prover_success(self):
        self._run(prefix_check=lambda *args: (False, "assumptions found"))
        self.assertEqual(self.state["runs"]["run-001"]["attempts"][0]["status"], "rejected")
        self.assertFalse((self.chain / "candidates/v001").exists())

    def test_failed_proof_cannot_adopt_or_start_measurement(self):
        def proof_fails(role, *args):
            report = self._role(role, *args)
            if role == "prover":
                report["answer"] = {"status": "failed", "reason": "could not close theorem"}
            return report
        self._run(call_role=proof_fails,
                  measure=lambda *args: self.fail("measurement must not run after failed proof"))
        attempt = self.state["runs"]["run-001"]["attempts"][0]
        self.assertEqual(attempt["status"], "rejected")
        self.assertEqual(attempt["proof_cost"]["wall_seconds"], 5)
        self.assertEqual(experiment.worker_feedback(self.state, "run-001")["attempts"][0]["feedback_summary"],
                         "proof_failed")
        self.assertNotIn("could not close theorem",
                         json.dumps(experiment.worker_feedback(self.state, "run-001")))
        self.assertFalse((self.chain / "candidates/v001").exists())

    def test_reformulator_receives_only_own_run_feedback(self):
        self.state["runs"]["run-002"]["attempts"].append(
            {"id": "attempt-001", "status": "rejected",
             "transformation_summary": "CROSS_RUN_SECRET", "feedback_summary": "secret"})
        self.state["held_out_baseline"] = {"secret": "HELD_OUT_SECRET"}
        contexts = []
        def inspect_context(role, *args):
            contexts.append((role, args[3]))
            return self._role(role, *args)
        self._run(syntax_check=lambda *args: (False, "shape invalid"),
                  call_role=inspect_context)
        self.assertEqual(len(contexts), 1)
        self.assertEqual(contexts[0][0], "reformulator")
        self.assertNotIn("CROSS_RUN_SECRET", json.dumps(contexts[0][1]))
        self.assertNotIn("HELD_OUT_SECRET", json.dumps(contexts[0][1]))

    def test_incomplete_measurement_cannot_adopt(self):
        with self.assertRaises(execute.ExecutionError):
            self._run(measure=lambda *args: batches(experiment.EVAL_SEEDS, status="incomplete"))
        self.assertFalse((self.chain / "candidates/v001").exists())
        execute.stop_after_error(self.state, self.evidence, RuntimeError("incomplete"))
        attempt = self.state["runs"]["run-001"]["attempts"][0]
        self.assertEqual(attempt["status"], "rejected")
        self.assertEqual(attempt["proof_cost"]["status"], "unavailable")

    def test_failed_candidate_derivation_counts_rejection_and_continues_run(self):
        self._run(measure=lambda *args: (_ for _ in ()).throw(
            execute.ProposalRejected("derivation_or_execution_failed: no scheduler")))
        attempt = self.state["runs"]["run-001"]["attempts"][0]
        self.assertEqual(attempt["status"], "rejected")
        self.assertEqual(attempt["proof_cost"]["wall_seconds"], 5)
        self.assertEqual(attempt["feedback_summary"], "derivation_or_execution_failed")
        self.assertIsNone(self.state["runs"]["run-001"]["stop_reason"])
        self.assertFalse((self.chain / "candidates/v001").exists())

    def test_adoption_occurs_only_after_all_checks_and_measurement(self):
        self._run()
        self.assertEqual(self.state["runs"]["run-001"]["adopted"][0]["id"], "v001")
        self.assertTrue((self.chain / "candidates/v001/Equivalence.v").is_file())
        self.assertEqual(execute.digest(self.chain / "candidates/v001/Candidate.v"),
                         self.state["runs"]["run-001"]["adopted"][0]["candidate_sha256"])

    def test_author_bundles_exclude_other_runs_and_old_proofs(self):
        previous = self.chain / "candidates/v001"
        previous.mkdir(parents=True)
        (previous / "Candidate.v").write_text("old\n")
        (previous / "Equivalence.v").write_text("private proof strategy\n")
        bundle = execute.role_inputs(self.root, self.chain)
        self.assertIn("property/candidates/v001/Candidate.v", bundle)
        self.assertFalse(any("Equivalence" in key for key in bundle))
        self.assertFalse(any("run-002" in str(value) for value in bundle.values()))

    def test_syntax_result_must_bind_exact_staged_candidate(self):
        staged = self.evidence / "syntax-stage"
        candidate = staged / "candidates/v001/Candidate.v"
        candidate.parent.mkdir(parents=True)
        (staged / "Original.v").write_text("fixed original\n")
        candidate.write_text("Inductive predicate : nat -> Prop := c : predicate 0.\n")
        frozen = {"sources": {execute.SOURCE_FILES[0]:
                              execute.digest(self.root / execute.SOURCE_FILES[0])}}
        evidence = self.evidence / "syntax-evidence"
        evidence.mkdir()
        def fake_command(command, **kwargs):
            result_dir = Path(command[command.index("--evidence-dir") + 1])
            result_dir.mkdir()
            (result_dir / "result.json").write_text(json.dumps({
                "status": "passed", "candidate": "v001", "source_hashes": {
                    "specification/cedar/Spec.v": frozen["sources"][execute.SOURCE_FILES[0]],
                    "property/Original.v": execute.digest(staged / "Original.v"),
                    "property/candidates/v001/Candidate.v": "wrong-candidate-hash"}}))
            return SimpleNamespace(returncode=0)
        with mock.patch.object(execute, "assert_frozen"), \
             mock.patch.object(execute, "checked_command", side_effect=fake_command):
            with self.assertRaises(execute.ExecutionError):
                execute.syntax_check(self.root, staged, "v001", evidence, frozen)

    def test_syntax_rejection_with_partial_hashes_is_a_proposal_failure(self):
        staged = self.evidence / "syntax-failure-stage"
        candidate = staged / "candidates/v001/Candidate.v"
        candidate.parent.mkdir(parents=True)
        (staged / "Original.v").write_text("fixed original\n")
        candidate.write_text("Definition predicate := True.\n")
        frozen = {"sources": {execute.SOURCE_FILES[0]:
                              execute.digest(self.root / execute.SOURCE_FILES[0])}}
        evidence = self.evidence / "syntax-failure-evidence"
        evidence.mkdir()
        def fake_command(command, **kwargs):
            result_dir = Path(command[command.index("--evidence-dir") + 1])
            result_dir.mkdir()
            (result_dir / "result.json").write_text(json.dumps({
                "status": "failed", "candidate": "v001", "source_hashes": {
                    "property/candidates/v001/Candidate.v": execute.digest(candidate)},
                "error": "predicate must be Inductive"}))
            return SimpleNamespace(returncode=1)
        with mock.patch.object(execute, "assert_frozen"), \
             mock.patch.object(execute, "checked_command", side_effect=fake_command):
            passed, reason = execute.syntax_check(self.root, staged, "v001", evidence, frozen)
        self.assertFalse(passed)
        self.assertIn("Inductive", reason)

    def test_explicit_candidate_benchmark_failure_is_proposal_rejection(self):
        staged = self.evidence / "benchmark-stage"
        staged.mkdir()
        (staged / "Original.v").write_text("fixed original\n")
        frozen = {"sources": {execute.SOURCE_FILES[0]:
                              execute.digest(self.root / execute.SOURCE_FILES[0])},
                  "tools": {name: execute.digest(self.root / name)
                            for name in ("scripts/cedar/benchmark.py", "scripts/cedar/Support.v",
                                         "scripts/cedar/driver.ml", "scripts/cedar/serialization.py",
                                         "environment/env.sh")}}
        evidence = self.evidence / "benchmark-failure-evidence"
        evidence.mkdir()
        def fake_command(command, **kwargs):
            output = Path(command[command.index("--output-dir") + 1])
            output.mkdir(parents=True)
            (output / "result.json").write_text(json.dumps({
                "status": "failed", "candidate": "v001", "seed": 101,
                "attempts": experiment.ATTEMPTS_PER_SEED, "size": experiment.SIZE,
                "test_mode": False, "prefix_check": "prefix-audit.json",
                "source_hashes": {"Spec.v": frozen["sources"][execute.SOURCE_FILES[0]],
                                  "Original.v": execute.digest(staged / "Original.v")},
                "tool_hashes": {"benchmark.py": frozen["tools"]["scripts/cedar/benchmark.py"],
                                "Support.v": frozen["tools"]["scripts/cedar/Support.v"],
                                "driver.ml": frozen["tools"]["scripts/cedar/driver.ml"],
                                "serialization.py": frozen["tools"]["scripts/cedar/serialization.py"],
                                "env.sh": frozen["tools"]["environment/env.sh"]},
                "error": "scheduler could not derive"}))
            return SimpleNamespace(returncode=1)
        with mock.patch.object(execute, "assert_frozen"), \
             mock.patch.object(execute, "checked_command", side_effect=fake_command):
            with self.assertRaisesRegex(execute.ProposalRejected, "scheduler could not derive"):
                execute.benchmark_batch(self.root, staged, "v001", 101, evidence, frozen)

    def test_completed_benchmark_requires_actual_scheduler_outcome(self):
        output = self.evidence / "completed-benchmark"
        output.mkdir()
        (output / "sources").mkdir()
        (output / "sources/theorem.ml").write_text("(* extracted checker *)\n")
        scheduler = output / "scheduler.log"
        scheduler.write_text("Theorem Schedule:\nPieces:\n"
                             "*** Gave up! Passed only 3500 tests\n"
                             "Discarded: 20000\n")
        provenance = {"derivation": {"status": "succeeded", "log": "scheduler.log",
                                     "extracted_checker": "sources/theorem.ml"},
                      "quickchick": {"status": "gave_up", "tests": 3500,
                                     "discards": 20000,
                                     "summary": "*** Gave up! Passed only 3500 tests\nDiscarded: 20000",
                                     "log": "scheduler.log"}}
        execute.check_benchmark_completion(provenance, output)
        with self.assertRaisesRegex(execute.ExecutionError, "internal QuickChick"):
            execute.check_benchmark_completion({**provenance,
                "quickchick": {**provenance["quickchick"], "status": "passed"}}, output)
        scheduler.write_text("Theorem Schedule:\nPieces:\n")
        with self.assertRaisesRegex(execute.ExecutionError, "unrecognized"):
            execute.check_benchmark_completion(provenance, output)
        scheduler.write_text("Theorem Schedule:\nPieces:\n"
                             "*** Failed after 6 tests and 0 shrinks. (0 discards)\n")
        with self.assertRaisesRegex(execute.ExecutionError, "internal QuickChick"):
            execute.check_benchmark_completion(provenance, output)

    def test_command_timeout_reaps_descendant_process_group(self):
        marker = self.evidence / "descendant-survived"
        child = ("import time; from pathlib import Path; time.sleep(0.4); "
                 f"Path({str(marker)!r}).write_text('bad')")
        parent = ("import subprocess,sys,time; "
                  f"subprocess.Popen([sys.executable,'-c',{child!r}]); time.sleep(30)")
        log = self.evidence / "timeout.json"
        with self.assertRaises(execute.ExecutionError):
            execute.checked_command([sys.executable, "-c", parent], cwd=self.root,
                                    log=log, timeout=0.05)
        time.sleep(0.5)
        self.assertFalse(marker.exists())
        self.assertEqual(json.loads(log.read_text())["status"], "timeout")


if __name__ == "__main__":
    unittest.main()
