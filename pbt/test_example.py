"""Real process smoke tests for Lean samples and external Python observations."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from pbt.run import ObservationError, Sample, check_observation, execute, parse_sample


class ExampleIntegrationTest(unittest.TestCase):
    def test_certified_generator_passes_strict_axiom_audit(self) -> None:
        root: Path = Path(__file__).resolve().parents[1]
        result = subprocess.run(
            (
                sys.executable, "-m", "pbt.verify", "--module", "pbt.example.Generator",
                "--proof", "Example.correctGenerator", "--expected-type",
                "ExampleGoals.CorrectGen ExampleGoals.Premise", "--timeout-seconds", "60",
            ),
            cwd=root, capture_output=True, text=True, check=False, timeout=90,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("zero transitive axioms", result.stdout)

    def test_external_programs_are_reproducible_and_replayable(self) -> None:
        root: Path = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory(dir=root / "test_cases") as temporary:
            first: Path = Path(temporary) / "first"
            second: Path = Path(temporary) / "second"
            for output in (first, second):
                result: subprocess.CompletedProcess[str] = execute(
                    (
                        sys.executable, "-m", "pbt.run", "--implementation", sys.executable,
                        "--output", str(output), "--count", "4", "--size", "8", "--seed", "12",
                    ),
                    root,
                )
                self.assertIn("Passed 4 external programs", result.stdout)
            for index, expected in enumerate((6, 8, 10, 12)):
                first_case: Path = first / f"case-{index:06d}"
                second_case: Path = second / f"case-{index:06d}"
                sample: Sample = parse_sample((first_case / "sample.json").read_text(encoding="utf-8"))
                self.assertEqual(sample, Sample(index, 8, 12 + index, expected))
                for name in ("program.py", "sample.json", "observation.json"):
                    self.assertEqual((first_case / name).read_bytes(), (second_case / name).read_bytes())
                replay: subprocess.CompletedProcess[str] = execute(
                    (sys.executable, str(first_case / "program.py")), root
                )
                self.assertEqual(check_observation(expected, replay), expected)
            repeated: subprocess.CompletedProcess[str] = subprocess.run(
                (
                    sys.executable, "-m", "pbt.run", "--implementation", sys.executable,
                    "--output", str(first), "--count", "4", "--size", "8", "--seed", "12",
                ),
                cwd=root, capture_output=True, text=True, check=False, timeout=60,
            )
            self.assertNotEqual(repeated.returncode, 0)
            self.assertIn("FileExistsError", repeated.stderr)
            self.assertEqual(len(list(first.glob("case-*"))), 4)

    def test_wrong_external_observation_is_rejected(self) -> None:
        root: Path = Path(__file__).resolve().parents[1]
        with tempfile.TemporaryDirectory(dir=root / "test_cases") as temporary:
            source: Path = Path(temporary) / "incorrect.py"
            source.write_text("print(8 + 1)\n", encoding="utf-8")
            result: subprocess.CompletedProcess[str] = execute((sys.executable, str(source)), root)
            with self.assertRaisesRegex(ObservationError, "expected=8, observed=9"):
                check_observation(8, result)

    def test_sample_decoder_requires_natural_fields(self) -> None:
        valid: str = json.dumps({"index": 0, "size": 3, "seed": 2, "input": 4, "extra": "ignored"})
        self.assertEqual(parse_sample(valid), Sample(0, 3, 2, 4))
        with self.assertRaisesRegex(ValueError, "'input' must be a natural number"):
            parse_sample('{"index":0,"size":3,"seed":2,"input":true}')


if __name__ == "__main__":
    unittest.main()
