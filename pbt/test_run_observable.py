"""End-to-end tests use certified Lean sampling/checking and a real child process."""

import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class ObservableRunTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temporary = tempfile.TemporaryDirectory(prefix="observable-run-test-")
        cls.project = Path(cls.temporary.name)
        (cls.project / "pbt").mkdir()
        (cls.project / "Fixtures").mkdir()
        for filename in ("CorrectGen.lean", "GoalTools.lean", "Observable.lean"):
            shutil.copyfile(ROOT / "pbt" / filename, cls.project / "pbt" / filename)
        shutil.copyfile(ROOT / "lean-toolchain", cls.project / "lean-toolchain")
        shutil.copyfile(ROOT / "lake-manifest.json", cls.project / "lake-manifest.json")
        (cls.project / ".lake").mkdir()
        (cls.project / ".lake/packages").symlink_to(ROOT / ".lake/packages", target_is_directory=True)
        (cls.project / "lakefile.toml").write_text(
            'name = "runner_test"\n[[lean_lib]]\nname = "pbt"\n'
            '[[lean_lib]]\nname = "Fixtures"\n'
            '[[require]]\nname = "palamedes"\n'
            'git = "https://github.com/hgoldstein95/palamedes-lean"\n'
            'rev = "c2012b84fc4ad8ee03e3528838175b959fcc9cf8"\n')
        (cls.project / "Fixtures/Spec.lean").write_text(
            'import Lean\nnamespace Fixture\ndef Eval (i o : Nat) : Prop := o = i\nend Fixture\n')
        cls.manifest = cls.project / "manifest.json"
        cls.manifest.write_text(json.dumps({"schema_version": 1, "namespace": "Fixture",
            "types": {"nat": {"kind": "primitive", "lean": "Nat"}},
            "relations": {"Eval": {"lean": "Fixture.Eval", "inputs": [0],
                "arguments": [{"type": "nat"}, {"type": "nat"}]}}}))
        cls.config = cls.project / "observations.toml"
        cls.config.write_text('schema_version = 1\n[[observations]]\nid = "eval"\n'
                              'relation = "Eval"\nobserve = ["%1"]\n')
        from pbt.observations import generate_view
        generate_view(cls.project, cls.manifest, cls.config, "eval", "Fixtures.Spec",
                      "View", cls.project / "Fixtures/View.lean", 60)
        (cls.project / "Fixtures/Property.lean").write_text('''import Fixtures.View
namespace Property
def Premise (_ : View.Input) : Prop := True
def Target (i : View.Input) (o : View.Observation) : Prop := o = i
def check (i : View.Input) (o : View.Observation) : Bool := decide (o = i)
theorem check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o) := by
  intro i o _
  exact ⟨of_decide_eq_true (p := o = i), decide_eq_true (p := o = i)⟩
def EmptyPremise (_ : View.Input) : Prop := False
theorem empty_check_correct : ∀ i o, EmptyPremise i → (check i o = true ↔ Target i o) := by
  intro i o impossible
  exact False.elim impossible
end Property
''')
        (cls.project / "Fixtures/Generator.lean").write_text('''import Fixtures.Property
import pbt.CorrectGen
def correctGenerator : CorrectGen Property.Premise := Gen.CorrectGen.s_arbNat
''')
        cls.adapter = cls.project / "adapter.py"
        (cls.project / "Fixtures/Generic.lean").write_text('''import pbt.CorrectGen
def genericNats : CorrectGen (fun _ : Nat => True) := Gen.CorrectGen.s_arbNat
''')
        cls.adapter.write_text('''import json, sys, time
data = json.load(sys.stdin)
mode = sys.argv[1]
if mode == "timeout": time.sleep(10)
if mode == "crash": raise SystemExit(7)
if mode == "malformed": print("not JSON")
elif mode == "wrong_type": print(json.dumps({"observation": "not a Nat"}))
elif mode == "duplicate": print('{"observation": 7, "observation": 7}')
else: print(json.dumps({"observation": data["input"] + (1 if mode == "wrong" else 0)}))
''')

    @classmethod
    def tearDownClass(cls):
        cls.temporary.cleanup()

    def options(self, output, mode="correct", **updates):
        from pbt.run_observable import RunOptions
        values = dict(manifest=self.manifest, config=self.config, observation_id="eval",
            spec_module="Fixtures.Spec", view_module="Fixtures.View", view_namespace="View",
            property_module="Fixtures.Property", premise="Property.Premise", target="Property.Target",
            check="Property.check", check_correct="Property.check_correct",
            generator_module="Fixtures.Generator", generator="correctGenerator",
            adapter=(sys.executable, str(self.adapter), mode), output=output,
            count=2, size=4, seed=7, timeout_seconds=60, implementation_timeout_seconds=1)
        values.update(updates)
        return RunOptions(**values)

    def test_correct_and_incorrect_actual_outputs_are_distinguished_and_saved(self):
        from pbt.run_observable import run_observable
        for mode, status, tested in [("correct", "passed", 2), ("wrong", "failed", 1)]:
            output = self.project / ("run-" + mode)
            result = run_observable(self.project, self.options(output, mode))
            self.assertEqual((result.status, result.evaluated), (status, tested))
            self.assertEqual(result.skipped, 0)
            samples = [json.loads(line) for line in (output / "samples.jsonl").read_text().splitlines()]
            self.assertTrue(all(0 <= sample["input"] <= 4 for sample in samples))
            if mode == "correct":
                replayed_inputs = [sample["input"] for sample in samples]
            else:
                self.assertEqual([sample["input"] for sample in samples], replayed_inputs)
            self.assertTrue(all(set(sample) == {"index", "size", "seed", "input"} for sample in samples))
            case = output / "case-000000"
            self.assertEqual(json.loads((case / "sample.json").read_text())["input"], samples[0]["input"])
            self.assertEqual(json.loads((case / "observation.json").read_text())["observation"],
                             samples[0]["input"] + (mode == "wrong"))
            self.assertEqual(json.loads((output / "result.json").read_text())["status"], status)
            with self.assertRaises(FileExistsError):
                run_observable(self.project, self.options(output, mode))

    def test_execution_errors_never_pass_and_preserve_diagnostics(self):
        from pbt.run_observable import run_observable
        for mode in ("crash", "malformed", "timeout", "wrong_type", "duplicate"):
            with self.subTest(mode=mode):
                output = self.project / ("run-" + mode)
                result = run_observable(self.project, self.options(output, mode))
                self.assertEqual((result.status, result.evaluated), ("error", 0))
                self.assertTrue(json.loads((output / "result.json").read_text())["error"])
                self.assertTrue((output / "case-000000/process.json").exists())

    def test_empty_premise_rejects_generator_before_execution(self):
        from pbt.run_observable import run_observable
        output = self.project / "empty-premise"
        with self.assertRaises(ChildProcessError) as raised:
            run_observable(self.project, self.options(output,
                premise="Property.EmptyPremise", check_correct="Property.empty_check_correct"))
        self.assertIn("correctGenerator", str(raised.exception))
        self.assertFalse(output.exists())

    def test_reusable_generator_need_not_import_the_property_or_view(self):
        from pbt.run_observable import run_observable
        output = self.project / "generic-generator"
        result = run_observable(self.project, self.options(Path("generic-generator"),
            manifest=Path("manifest.json"), config=Path("observations.toml"),
            generator_module="Fixtures.Generic", generator="genericNats", count=1))
        self.assertEqual((result.status, result.evaluated), ("passed", 1), result.error)
        self.assertTrue((output / "result.json").is_file())

    def test_zero_count_and_changed_profile_are_rejected_before_execution(self):
        from pbt.run_observable import run_observable
        with self.assertRaises(ValueError):
            run_observable(self.project, self.options(self.project / "zero", count=0))
        changed = self.project / "changed.toml"
        changed.write_text(self.config.read_text().replace('id = "eval"', 'id = "other"'))
        output = self.project / "changed-profile"
        with self.assertRaises(ValueError):
            run_observable(self.project, self.options(output, config=changed, observation_id="other"))
        self.assertFalse(output.exists())
        link = self.project / "existing-link"
        link.symlink_to(self.project / "missing-target", target_is_directory=True)
        with self.assertRaises(FileExistsError):
            run_observable(self.project, self.options(link))
        self.assertFalse((self.project / "missing-target").exists())


if __name__ == "__main__":
    unittest.main()
