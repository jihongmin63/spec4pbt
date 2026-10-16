"""Real Lean tests for the observable certification and execution boundary."""
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

REPOSITORY = Path(__file__).resolve().parents[1]

GOOD = '''import Fixtures.View
namespace Property
def Premise (_ : View.Input) : Prop := True
def Target (i : View.Input) (o : View.Observation) : Prop := o = i
def check (i : View.Input) (o : View.Observation) : Bool := decide (o = i)
theorem check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o) := by
  intro i o _
  exact ⟨of_decide_eq_true (p := o = i), decide_eq_true (p := o = i)⟩
end Property
'''


class ObservableIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.temp = tempfile.TemporaryDirectory(prefix="observable-test-")
        cls.project = Path(cls.temp.name)
        (cls.project / "pbt").mkdir()
        (cls.project / "Fixtures").mkdir()
        for name in ["GoalTools.lean", "Observable.lean"]:
            source = REPOSITORY / "pbt" / name
            if source.exists():
                shutil.copyfile(source, cls.project / "pbt" / name)
        shutil.copyfile(REPOSITORY / "lean-toolchain", cls.project / "lean-toolchain")
        (cls.project / "lakefile.toml").write_text('name = "observable_test"\n[[lean_lib]]\nname = "pbt"\n[[lean_lib]]\nname = "Fixtures"\n')
        (cls.project / "Fixtures" / "View.lean").write_text('import Lean\nnamespace View\nabbrev Input := Nat\nabbrev Observation := Nat\ndef profileId : String := "fixture-profile"\ndef encodeInput (i : Input) : Lean.Json := Lean.toJson i\ndef decodeInput (j : Lean.Json) : Except String Input := Lean.fromJson? j\ndef decodeObservation (j : Lean.Json) : Except String Observation := Lean.fromJson? j\nend View\n')

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def certify(self, source=GOOD, **options):
        from pbt.verify_observable import verify_observable
        (self.project / "Fixtures" / "Property.lean").write_text(source)
        return verify_observable(self.project, "Fixtures.View", "View", "Fixtures.Property",
                                 "Property.Premise", "Property.Target", "Property.check",
                                 "Property.check_correct", 90, **options)

    def test_valid_checker_runs_actual_observation(self):
        checker = self.certify(expected_profile_id="fixture-profile")
        self.assertTrue(checker.run(7, 7))
        self.assertFalse(checker.run(7, 8))
        self.assertEqual(checker.profile_id, "fixture-profile")
        self.assertTrue(checker.identity)

    def test_property_codec_instance_cannot_change_actual_values(self):
        checker = self.certify(GOOD + """
instance (priority := 2000) : Lean.FromJson Nat where
  fromJson? _ := .ok 0
""")
        self.assertTrue(checker.run(7, 7))
        self.assertFalse(checker.run(7, 8))

    def test_property_boolean_codec_cannot_forge_checker_result(self):
        checker = self.certify(GOOD + """
instance (priority := 2000) : Lean.ToJson Bool where
  toJson _ := .bool true
""")
        self.assertFalse(checker.run(7, 8))

    def test_property_cannot_replace_frozen_transport_wrapper(self):
        with self.assertRaises(ChildProcessError) as raised:
            self.certify(GOOD + """
def wrongDecoder (_ : Lean.Json) : Except String View.Observation := .ok 0
attribute [implemented_by wrongDecoder] View.decodeObservation
""")
        self.assertIn("Cannot add attribute `[implemented_by]`", str(raised.exception))

    def test_invalid_driver_json_exits_nonzero(self):
        checker = self.certify()
        for invalid in ['oops', '{}', '[]', '{"input":7}',
                        '{"input":"bad","observation":7}',
                        '{"input":7,"observation":7,"extra":0}',
                        '{"input":7,"observation":7}\n{}']:
            with self.subTest(invalid=invalid):
                result = subprocess.run(checker.command, cwd=self.project, input=invalid,
                                        text=True, capture_output=True, timeout=90)
                self.assertNotEqual(result.returncode, 0, result.stdout)

    def test_rejects_invalid_declarations(self):
        variants = {
            "wrong observation": GOOD.replace('(o : View.Observation)', '(o : Int)').replace('o = i', 'o = Int.ofNat i'),
            "sorry proof": GOOD[:GOOD.index('theorem check_correct')] + 'theorem check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o) := by sorry\nend Property\n',
            "false proof": GOOD.replace('exact ⟨of_decide_eq_true (p := o = i), decide_eq_true (p := o = i)⟩', 'exact True.intro'),
            "axiom proof": GOOD[:GOOD.index('theorem check_correct')] + 'axiom check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o)\nend Property\n',
            "extra hypothesis": GOOD.replace('theorem check_correct :', 'theorem check_correct (_assumption : False) :'),
            "noncomputable": GOOD.replace('def check (', 'noncomputable def check ('),
            "unsafe": GOOD.replace('def check (', 'unsafe def check ('),
            "partial": """import Fixtures.View
namespace Property
def Premise (_ : View.Input) : Prop := True
partial def check (i : View.Input) (o : View.Observation) : Bool := check i o
def Target (i : View.Input) (o : View.Observation) : Prop := check i o = true
theorem check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o) := by
  intro i o _
  exact Iff.rfl
end Property
""",
            "runtime override": GOOD.replace('def check (', 'def wrong (i : View.Input) (o : View.Observation) : Bool := false\n@[implemented_by wrong] def check ('),
            "checker sorry": """import Fixtures.View
namespace Property
def Premise (_ : View.Input) : Prop := True
def check (_ : View.Input) (_ : View.Observation) : Bool := by sorry
def Target (i : View.Input) (o : View.Observation) : Prop := check i o = true
theorem check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o) := by
  intro i o _
  exact Iff.rfl
end Property
""",
            "unused axiom": GOOD.replace('namespace Property', 'namespace Property\naxiom unused : True'),
        }
        diagnostics = {
            "wrong observation": "type mismatch", "sorry proof": "sorryax",
            "false proof": "type mismatch", "axiom proof": "forbidden axiom",
            "extra hypothesis": "type mismatch", "noncomputable": "noncomputable",
            "unsafe": "unsafe", "partial": "partial",
            "runtime override": "runtime implementation override",
            "checker sorry": "sorryax", "unused axiom": "unused",
        }
        for label, source in variants.items():
            with self.subTest(case=label):
                with self.assertRaises((ChildProcessError, ValueError)) as raised:
                    self.certify(source)
                self.assertIn(diagnostics[label], str(raised.exception).lower())

    def test_profile_mismatch_and_stale_sources_rejected(self):
        with self.assertRaises(ValueError):
            self.certify(expected_profile_id="different")
        checker = self.certify()
        artifact = self.project / ".lake" / "build" / "lib" / "lean" / "Fixtures" / "Property.olean"
        original = artifact.read_bytes()
        try:
            artifact.write_bytes(original + b"modified artifact")
            with self.assertRaises(ValueError):
                checker.run(7, 7)
        finally:
            artifact.write_bytes(original)
        source = self.project / "Fixtures" / "Property.lean"
        source.write_text(GOOD.replace('decide (o = i)', 'by sorry'))
        with self.assertRaises(ValueError):
            checker.run(7, 7)
        with self.assertRaises(ChildProcessError):
            self.certify(source.read_text())

    def test_missing_observation_codec_rejected_during_view_compilation(self):
        source = self.project / "Fixtures" / "NoCodec.lean"
        source.write_text("""import Lean
namespace NoCodec
abbrev Input := Nat
inductive Observation where | value
def profileId : String := "no-codec"
def encodeInput (i : Input) : Lean.Json := Lean.toJson i
def decodeInput (j : Lean.Json) : Except String Input := Lean.fromJson? j
def decodeObservation (j : Lean.Json) : Except String Observation := Lean.fromJson? j
def Premise (_ : Input) : Prop := True
def Target (_ : Input) (_ : Observation) : Prop := True
def check (_ : Input) (_ : Observation) : Bool := true
theorem check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o) := by
  intro i o _
  exact ⟨fun _ => True.intro, fun _ => rfl⟩
end NoCodec
""")
        from pbt.verify_observable import verify_observable
        with self.assertRaises(ChildProcessError) as raised:
            verify_observable(self.project, "Fixtures.NoCodec", "NoCodec", "Fixtures.NoCodec",
                              "NoCodec.Premise", "NoCodec.Target", "NoCodec.check",
                              "NoCodec.check_correct", 90)
        self.assertIn("Lean.FromJson Observation", str(raised.exception))

    def test_compiler_rewrites_cannot_forge_certified_runtime(self):
        for scoped in [False, True]:
            replacement = """def helper (i : View.Input) (o : View.Observation) : Bool := decide (o = i)
def wrong (_ : View.Input) (_ : View.Observation) : Bool := true
"""
            if scoped:
                replacement += "theorem poison : helper = wrong := by sorry\nsection\nattribute [local csimp] poison\n"
            else:
                replacement += "@[csimp] theorem poison : helper = wrong := by sorry\n"
            replacement += "def check (i : View.Input) (o : View.Observation) : Bool := helper i o"
            if scoped:
                replacement += "\nend"
            source = GOOD.replace("def check (i : View.Input) (o : View.Observation) : Bool := decide (o = i)", replacement)
            with self.subTest(scoped=scoped):
                with self.assertRaises(ChildProcessError) as raised:
                    self.certify(source)
                self.assertIn("compiler policy", str(raised.exception))

    def test_source_edit_during_real_lean_audit_cannot_bind_old_code(self):
        from unittest.mock import patch
        from pbt.verify_observable import run_checked as real_run_checked

        def concurrent_edit(command, project, timeout):
            output = real_run_checked(command, project, timeout)
            if len(command) == 4 and command[2] == "lean" and command[-1].endswith("/Audit.lean"):
                source = project / "Fixtures" / "Property.lean"
                source.write_text(source.read_text() + "\n-- concurrent source edit\n")
            return output

        with patch("pbt.verify_observable.run_checked", side_effect=concurrent_edit):
            with self.assertRaises(ValueError) as raised:
                self.certify()
        self.assertIn("changed during certification", str(raised.exception))

    def test_declarations_must_belong_to_supplied_property_module(self):
        from pbt.verify_observable import verify_observable
        self.certify()
        (self.project / "Fixtures" / "Alias.lean").write_text('import Fixtures.Property\n')
        with self.assertRaises(ChildProcessError):
            verify_observable(self.project, "Fixtures.View", "View", "Fixtures.Alias",
                              "Property.Premise", "Property.Target", "Property.check",
                              "Property.check_correct", 90)


if __name__ == "__main__":
    unittest.main()
