"""Re-measurement gates and bookkeeping; measurement itself is replaced."""

import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

from scripts.cedar import execute, experiment, remeasure


def counts(seeds, valid):
    return {seed: {"status": "completed", "attempts": experiment.ATTEMPTS_PER_SEED,
                   "confirmed_valid": valid, "confirmed_invalid": 0,
                   "no_result": experiment.ATTEMPTS_PER_SEED - valid, "undetermined": 0}
            for seed in seeds}


class RemeasureTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="cedar-remeasure-")
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.prop = self.root / "properties/cedar_no_type_error"
        self.source = self.prop / "experiments/source"
        (self.prop / "Original.v").parent.mkdir(parents=True)
        (self.prop / "Original.v").write_text("(* original *)\n")
        artifacts = []
        for run_id, count in zip(experiment.RUN_IDS, (2, 1, 0)):
            chain = self.source / run_id
            chain.mkdir(parents=True)
            (chain / "Original.v").write_text("(* original *)\n")
            for index in range(1, count + 1):
                version = chain / f"candidates/v{index:03d}"
                version.mkdir(parents=True)
                for name in ("Candidate.v", "Equivalence.v"):
                    path = version / name
                    path.write_text(f"(* {run_id} {index} {name} *)\n")
                    artifacts.append({"path": path.relative_to(self.root).as_posix(),
                                      "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        self.audit = {"status": "passed", "adopted_artifacts": artifacts}
        (self.source / "final-audit.json").write_text(json.dumps(self.audit))
        self.frozen = {"commit": "a" * 40, "tools": {},
                       "sources": {execute.SOURCE_FILES[1]: hashlib.sha256(
                           b"(* original *)\n").hexdigest()}}
        self.calls = []

    def fake_measure(self, _root, staged, candidate, seeds, where, _frozen):
        self.calls.append((candidate, tuple(seeds), staged.name, where.name))
        if candidate != "P0":
            self.assertTrue((staged / "candidates" / candidate / "Equivalence.v").is_file())
        return counts(seeds, 10 if candidate == "P0" else 20)

    def run_remeasure(self):
        with mock.patch.object(execute, "ROOT", self.root), \
             mock.patch.object(execute, "frozen_manifest", return_value=self.frozen), \
             mock.patch.object(execute, "review_gate"), \
             mock.patch.object(execute, "assert_frozen"), \
             mock.patch.object(execute, "ensure_runtime_bridge"):
            return remeasure.remeasure("source", "again", self.root / "review.json",
                                       root=self.root, property_root=self.prop,
                                       measure=self.fake_measure)

    def test_measures_every_adopted_candidate_and_last_held_out(self):
        summary = json.loads(self.run_remeasure().read_text())
        eval_seeds, held = tuple(experiment.EVAL_SEEDS), tuple(experiment.HELD_OUT_SEEDS)
        self.assertEqual([call[:2] for call in self.calls], [
            ("P0", eval_seeds), ("P0", held), ("v001", eval_seeds), ("v002", eval_seeds),
            ("v002", held), ("v001", eval_seeds), ("v001", held)])
        run = summary["runs"]["run-001"]
        self.assertEqual([item["id"] for item in run["adopted"]], ["v001", "v002"])
        self.assertAlmostEqual(run["adopted"][0]["comparison"]["vs_P0"]["difference"], 0.001)
        self.assertEqual(run["held_out"]["candidate"], "v002")
        self.assertIsNone(summary["runs"]["run-003"]["held_out"])
        self.assertTrue((self.prop / ".runs/again/completion.json").is_file())

    def test_changed_adopted_file_stops_before_any_measurement(self):
        (self.source / "run-001/candidates/v002/Candidate.v").write_text("(* edited *)\n")
        with self.assertRaisesRegex(remeasure.RemeasureError, "differs from source audit"):
            self.run_remeasure()
        self.assertEqual(self.calls, [])
        self.assertFalse((self.prop / ".runs/again").exists())

    def test_existing_experiment_id_is_never_overwritten(self):
        (self.prop / ".runs/again").mkdir(parents=True)
        with self.assertRaisesRegex(remeasure.RemeasureError, "already exists"):
            self.run_remeasure()
        self.assertEqual(self.calls, [])


if __name__ == "__main__":
    unittest.main()
