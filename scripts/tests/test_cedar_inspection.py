"""Scripted independent inspection: gate logic and a real Coq candidate check."""

import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from scripts.cedar import execute, inspection

ROOT = Path(__file__).resolve().parents[2]
PROPERTY = ROOT / "properties/cedar_no_type_error"

CANDIDATE = '''Require Import List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
Import ListNotations.
Inductive predicate : Original.Input -> Prop :=
| intro : forall ets acts rs e es ty expr,
    WfSchema Original.entity_names (MkSchema ets acts) ->
    ActionSchemaToRequestTypes acts [] rs ->
    SchemaToEnvironments (MkSchema ets acts) rs (e :: es) ->
    WfCedarType Original.entity_names ty ->
    HasType (somepaths []) e expr ty ->
    predicate (Original.mkInput ets acts rs e es ty expr).
'''

EQUIVALENCE = '''Require Import Property.candidates.v001.Candidate.
Theorem equivalent : forall x, Original.predicate x <-> Candidate.predicate x.
Proof.
  intros [ets acts rs e es ty expr]; simpl; split.
  - intros [Hs [Hr [He [Ht Hp]]]]. exact (Candidate.intro _ _ _ _ _ _ _ Hs Hr He Ht Hp).
  - intros H. inversion H; subst; repeat split; assumption.
Qed.
'''


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


class SnapshotAndReportTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="cedar-inspection-")
        self.addCleanup(self.temp.cleanup)
        base = Path(self.temp.name)
        self.chain = base / "chain"
        self.staged = base / "staged"
        for root in (self.chain, self.staged):
            (root / "candidates/v001").mkdir(parents=True)
            (root / "Original.v").write_text("(* original *)\n")
            (root / "candidates/v001/Candidate.v").write_text("(* v001 *)\n")
            (root / "candidates/v001/Equivalence.v").write_text("(* proof 1 *)\n")
        (self.staged / "candidates/v002").mkdir()
        (self.staged / "candidates/v002/Candidate.v").write_text("(* v002 *)\n")
        (self.staged / "candidates/v002/Equivalence.v").write_text("(* proof 2 *)\n")
        self.original = sha(self.staged / "Original.v")
        self.selected = sha(self.staged / "candidates/v002/Candidate.v")

    def violations(self):
        return inspection.snapshot_violations(self.staged, self.chain, "v002",
                                              self.selected, self.original)

    def test_exact_snapshot_has_no_violation(self):
        self.assertEqual(self.violations(), [])

    def test_changed_adopted_candidate_or_proof_is_a_violation(self):
        (self.staged / "candidates/v001/Equivalence.v").write_text("(* other proof *)\n")
        self.assertIn("staged v001/Equivalence.v differs from the adopted chain",
                      self.violations())

    def test_changed_selected_candidate_and_extra_files_are_violations(self):
        (self.staged / "candidates/v002/Candidate.v").write_text("(* changed *)\n")
        (self.staged / "candidates/v002/Generator.v").write_text("(* forbidden *)\n")
        found = self.violations()
        self.assertIn("v002/Candidate.v differs from the proved candidate", found)
        self.assertTrue(any("unexpected files" in item for item in found))

    def test_skipped_or_extra_versions_are_violations(self):
        shutil.copytree(self.staged / "candidates/v002", self.staged / "candidates/v003")
        self.assertTrue(any("not adopted" in item for item in self.violations()))

    def report(self, directory, **changes):
        names = ["frozen_tools", "snapshot", "syntax", "equivalence_chain",
                 "derivation_probe", "sources_unchanged", "tools_unchanged"]
        log = directory / "check.log"
        log.write_text("passed\n")
        report = {"kind": inspection.CANDIDATE_KIND, "candidate": "v002",
                  "status": "passed", "violations": [],
                  "checks": [{"name": name, "status": "passed"} for name in names],
                  "commands": [{"returncode": 0, "log": str(log), "log_sha256": sha(log)}]}
        report.update(changes)
        path = directory / "result.json"
        path.write_text(json.dumps(report))
        return path, log

    def test_report_check_requires_all_passed_checks_and_unchanged_logs(self):
        directory = Path(self.temp.name)
        path, log = self.report(directory)
        inspection.check_candidate_report(path, "v002")
        with self.assertRaises(inspection.InspectionError):
            inspection.check_candidate_report(path, "v003")
        log.write_text("edited\n")
        with self.assertRaises(inspection.InspectionError):
            inspection.check_candidate_report(path, "v002")
        path, _ = self.report(directory, checks=[{"name": "snapshot", "status": "passed"}])
        with self.assertRaises(inspection.InspectionError):
            inspection.check_candidate_report(path, "v002")


class ToolReviewTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="cedar-tool-review-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "scripts/tests").mkdir(parents=True)
        self.frozen = {"commit": "b" * 40, "sources": {}, "tools": {}, "conditions": {}}

    def write_test(self, body):
        (self.root / "scripts/tests/test_probe.py").write_text(
            "import unittest\n\nclass Probe(unittest.TestCase):\n"
            f"    def test_probe(self):\n        {body}\n")

    def test_passing_suite_produces_bound_review(self):
        self.write_test("self.assertTrue(True)")
        path = inspection.tool_review(self.root, self.root / "review", self.frozen)
        review = inspection.check_tool_review(path, self.frozen)
        self.assertEqual(review["tests_run"], 1)
        self.assertFalse(list(self.root.rglob("__pycache__")))
        with self.assertRaises(inspection.InspectionError):
            inspection.check_tool_review(path, {**self.frozen, "commit": "c" * 40})
        Path(review["commands"][0]["log"]).write_text("Ran 1 test in 0.0s\n\nOK\n")
        with self.assertRaises(inspection.InspectionError):
            inspection.check_tool_review(path, self.frozen)

    def test_failing_suite_cannot_pass_review(self):
        self.write_test("self.assertTrue(False)")
        path = inspection.tool_review(self.root, self.root / "review", self.frozen)
        self.assertEqual(json.loads(path.read_text())["status"], "failed")
        with self.assertRaises(inspection.InspectionError):
            inspection.check_tool_review(path, self.frozen)


class RealCandidateInspectionTests(unittest.TestCase):
    """Runs syntax.py, check.py, and a short official derivation with real Coq."""

    def setUp(self):
        runs = PROPERTY / ".runs"
        runs.mkdir(parents=True, exist_ok=True)
        self.temp = tempfile.TemporaryDirectory(dir=runs, prefix="test-inspection-")
        self.addCleanup(self.temp.cleanup)
        base = Path(self.temp.name)
        self.chain = base / "chain"
        self.chain.mkdir()
        shutil.copy2(PROPERTY / "Original.v", self.chain / "Original.v")
        self.staged = base / "staged"
        (self.staged / "candidates/v001").mkdir(parents=True)
        shutil.copy2(PROPERTY / "Original.v", self.staged / "Original.v")
        (self.staged / "candidates/v001/Candidate.v").write_text(CANDIDATE)
        (self.staged / "candidates/v001/Equivalence.v").write_text(EQUIVALENCE)
        self.evidence = base / "evidence"
        self.evidence.mkdir()
        self.frozen = execute.frozen_manifest(ROOT)

    def test_real_candidate_passes_and_report_is_accepted(self):
        before = sorted(path.relative_to(self.staged) for path in self.staged.rglob("*"))
        report = inspection.inspect_candidate(
            ROOT, self.staged, self.chain, "v001",
            sha(self.staged / "candidates/v001/Candidate.v"), self.frozen,
            self.evidence, probe_attempts=5)
        self.assertEqual(report["status"], "passed", report["violations"])
        inspection.check_candidate_report(self.evidence / "inspection/result.json", "v001")
        self.assertEqual(report["derivation_probe"]["counts"]["generated"] +
                         report["derivation_probe"]["counts"]["discard"], 5)
        after = sorted(path.relative_to(self.staged) for path in self.staged.rglob("*"))
        self.assertEqual(before, after)

    def test_real_candidate_with_wrong_proof_fails_equivalence_chain(self):
        (self.staged / "candidates/v001/Equivalence.v").write_text(
            "Require Import Property.candidates.v001.Candidate.\n"
            "Theorem equivalent : forall x, Original.predicate x <-> Candidate.predicate x.\n"
            "Proof. Admitted.\n")
        report = inspection.inspect_candidate(
            ROOT, self.staged, self.chain, "v001",
            sha(self.staged / "candidates/v001/Candidate.v"), self.frozen,
            self.evidence, probe_attempts=5)
        self.assertEqual(report["status"], "failed")
        self.assertTrue(any(item.startswith("equivalence_chain")
                            for item in report["violations"]))
        self.assertFalse(any(check["name"] == "derivation_probe" for check in report["checks"]))


if __name__ == "__main__":
    unittest.main()
