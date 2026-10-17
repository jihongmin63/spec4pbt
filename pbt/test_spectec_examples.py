"""Native translated specs -> typed views -> real implementation observations."""

import json
from pathlib import Path
import sys
import tempfile
import unittest

from pbt.run_observable import RunOptions, run_observable


ROOT = Path(__file__).resolve().parents[1]


def example_options(example, output, mode="correct"):
    namespace = "Ae" if example == "ae" else "Partial"
    extra = (["--wrong"] if mode == "wrong" else []) if example == "ae" else [mode]
    return RunOptions(
        manifest=ROOT / f"specifications/{example}/manifest.json",
        config=ROOT / f"specifications/{example}/observations.toml",
        observation_id="value", spec_module=f"specifications.{example}.Spec",
        view_module=f"pbt.{example}.View", view_namespace=namespace + "View",
        property_module=f"pbt.{example}.Property", premise=namespace + "Property.Premise",
        target=namespace + "Property.Target", check=namespace + "Property.check",
        check_correct=namespace + "Property.check_correct",
        generator_module=f"pbt.{example}.Generator", generator=namespace + "Property.correctGenerator",
        adapter=(sys.executable, str(ROOT / f"pbt/{example}/adapter.py"), *extra),
        output=output, count=4, size=5, seed=0)


class SpectecExampleTests(unittest.TestCase):
    def test_arithmetic_correct_and_wrong_actual_output(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            for mode, expected in [("correct", "passed"), ("wrong", "failed")]:
                result = run_observable(ROOT, example_options("ae", base / mode, mode))
                self.assertEqual(result.status, expected, result.error)

    def test_hidden_record_changes_are_ignored_but_observed_violation_fails(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            for mode, expected in [("correct", "passed"), ("hidden-change", "passed"), ("wrong", "failed")]:
                result = run_observable(ROOT, example_options("record", base / mode, mode))
                self.assertEqual(result.status, expected, result.error)
            normal = json.loads((base / "correct/case-000000/process.json").read_text())
            changed = json.loads((base / "hidden-change/case-000000/process.json").read_text())
            self.assertEqual(json.loads(normal["stderr"])["TRACE"], 0)
            self.assertEqual(json.loads(changed["stderr"])["TRACE"], -999)
            self.assertEqual(normal["stdout"], changed["stdout"])


if __name__ == "__main__":
    unittest.main()
