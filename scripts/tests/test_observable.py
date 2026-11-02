"""Real Lean checks for executable declarations and frozen transport codecs."""

from pathlib import Path
import shutil
import tempfile
import unittest

from scripts.lean_tools import elaborate, rebuild_modules


from scripts.tests import ROOT as REPOSITORY, SCRATCH

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

VIEW = '''import Lean
namespace View
abbrev Input := Nat
abbrev Observation := Nat
def encodeInput (i : Input) : Lean.Json := Lean.toJson i
def decodeInput (j : Lean.Json) : Except String Input := Lean.fromJson? j
def decodeObservation (j : Lean.Json) : Except String Observation := Lean.fromJson? j
end View
'''


class ObservableIntegrationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        SCRATCH.mkdir(parents=True, exist_ok=True)
        cls.temp = tempfile.TemporaryDirectory(prefix="observable-test-", dir=SCRATCH)
        cls.project = Path(cls.temp.name)
        (cls.project / "Spec4Pbt").mkdir()
        (cls.project / "Fixtures").mkdir()
        for name in ["GoalTools.lean", "Observable.lean"]:
            shutil.copyfile(REPOSITORY / "scripts/lean/Spec4Pbt" / name, cls.project / "Spec4Pbt" / name)
        shutil.copyfile(REPOSITORY / "lean-toolchain", cls.project / "lean-toolchain")
        (cls.project / "lakefile.toml").write_text(
            'name = "observable_test"\n[[lean_lib]]\nname = "Spec4Pbt"\n[[lean_lib]]\nname = "Fixtures"\n',
            encoding="utf-8",
        )
        (cls.project / "Fixtures" / "View.lean").write_text(VIEW, encoding="utf-8")
        rebuild_modules(cls.project, ["Spec4Pbt.Observable", "Fixtures.View"], 90)

    @classmethod
    def tearDownClass(cls):
        cls.temp.cleanup()

    def audit_property(self, source=GOOD, extra=""):
        (self.project / "Fixtures" / "Property.lean").write_text(source, encoding="utf-8")
        rebuild_modules(self.project, ["Fixtures.Property"], 90)
        return elaborate(self.project, '''import Spec4Pbt.Observable
import Fixtures.Property
#spec4pbt_verify Property.Premise in_module Fixtures.Property : View.Input → Prop
#spec4pbt_verify Property.Target in_module Fixtures.Property : View.Input → View.Observation → Prop
#spec4pbt_verify Property.check in_module Fixtures.Property : View.Input → View.Observation → Bool
#spec4pbt_verify Property.check_correct in_module Fixtures.Property :
  ∀ (i : View.Input) (o : View.Observation),
    Property.Premise i → (Property.check i o = true ↔ Property.Target i o)
#spec4pbt_observable_executable Property.check
#spec4pbt_observable_transport View.encodeInput
#spec4pbt_observable_transport View.decodeInput
#spec4pbt_observable_transport View.decodeObservation
''' + extra, 90)

    def audit_transport(self, source):
        (self.project / "Fixtures" / "Transport.lean").write_text(source, encoding="utf-8")
        rebuild_modules(self.project, ["Fixtures.Transport"], 90)
        return elaborate(self.project, '''import Spec4Pbt.Observable
import Fixtures.Transport
#spec4pbt_observable_transport Transport.decode
''', 90)

    def test_valid_checker_executes_actual_observation(self):
        output = self.audit_property(extra='''#eval Property.check 7 7
#eval Property.check 7 8
''')
        self.assertEqual(output.splitlines()[-2:], ["true", "false"])

    def test_property_codec_instance_cannot_change_frozen_decoders(self):
        output = self.audit_property(GOOD + '''
instance (priority := 2000) : Lean.FromJson Nat where
  fromJson? _ := .ok 0
''', extra='''#eval View.decodeInput (Lean.Json.num 7)
#eval View.decodeObservation (Lean.Json.num 8)
''')
        self.assertEqual(output.splitlines()[-2:], ["Except.ok 7", "Except.ok 8"])

    def test_property_cannot_replace_frozen_transport_wrapper(self):
        with self.assertRaisesRegex(ChildProcessError, "Cannot add attribute.*implemented_by"):
            self.audit_property(GOOD + '''
def wrongDecoder (_ : Lean.Json) : Except String View.Observation := .ok 0
attribute [implemented_by wrongDecoder] View.decodeObservation
''')

    def test_rejects_invalid_declarations(self):
        variants = {
            "wrong observation": GOOD.replace('(o : View.Observation)', '(o : Int)').replace('o = i', 'o = Int.ofNat i'),
            "sorry proof": GOOD[:GOOD.index('theorem check_correct')] + 'theorem check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o) := by sorry\nend Property\n',
            "false proof": GOOD.replace('exact ⟨of_decide_eq_true (p := o = i), decide_eq_true (p := o = i)⟩', 'exact True.intro'),
            "axiom proof": GOOD[:GOOD.index('theorem check_correct')] + 'axiom check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o)\nend Property\n',
            "extra hypothesis": GOOD.replace('theorem check_correct :', 'theorem check_correct (_assumption : False) :'),
            "noncomputable": GOOD.replace('def check (', 'noncomputable def check ('),
            "unsafe": GOOD.replace('def check (', 'unsafe def check ('),
            "partial": '''import Fixtures.View
namespace Property
def Premise (_ : View.Input) : Prop := True
partial def check (i : View.Input) (o : View.Observation) : Bool := check i o
def Target (i : View.Input) (o : View.Observation) : Prop := check i o = true
theorem check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o) := by
  intro i o _
  exact Iff.rfl
end Property
''',
            "runtime override": GOOD.replace('def check (', 'def wrong (i : View.Input) (o : View.Observation) : Bool := false\n@[implemented_by wrong] def check ('),
            "checker sorry": '''import Fixtures.View
namespace Property
def Premise (_ : View.Input) : Prop := True
def check (_ : View.Input) (_ : View.Observation) : Bool := by sorry
def Target (i : View.Input) (o : View.Observation) : Prop := check i o = true
theorem check_correct : ∀ i o, Premise i → (check i o = true ↔ Target i o) := by
  intro i o _
  exact Iff.rfl
end Property
''',
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
                with self.assertRaises(ChildProcessError) as raised:
                    self.audit_property(source)
                self.assertIn(diagnostics[label], str(raised.exception).lower())

    def test_missing_observation_codec_rejected_during_view_compilation(self):
        source = self.project / "Fixtures" / "NoCodec.lean"
        source.write_text('''import Lean
namespace NoCodec
inductive Observation where | value
def decodeObservation (j : Lean.Json) : Except String Observation := Lean.fromJson? j
end NoCodec
''', encoding="utf-8")
        with self.assertRaisesRegex(ChildProcessError, "Lean.FromJson Observation"):
            rebuild_modules(self.project, ["Fixtures.NoCodec"], 90)

    def test_compiler_rewrites_cannot_forge_certified_runtime(self):
        for scoped in [False, True]:
            replacement = '''def helper (i : View.Input) (o : View.Observation) : Bool := decide (o = i)
def wrong (_ : View.Input) (_ : View.Observation) : Bool := true
'''
            if scoped:
                replacement += "theorem poison : helper = wrong := by sorry\nsection\nattribute [local csimp] poison\n"
            else:
                replacement += "@[csimp] theorem poison : helper = wrong := by sorry\n"
            replacement += "def check (i : View.Input) (o : View.Observation) : Bool := helper i o"
            if scoped:
                replacement += "\nend"
            source = GOOD.replace("def check (i : View.Input) (o : View.Observation) : Bool := decide (o = i)", replacement)
            with self.subTest(scoped=scoped):
                with self.assertRaisesRegex(ChildProcessError, "compiler policy"):
                    self.audit_property(source)

    def test_compiler_policy_rejects_custom_rewrites_even_with_kernel_proofs(self):
        source = GOOD + '''
def helper (n : Nat) : Nat := n
def replacement (n : Nat) : Nat := n
@[csimp] theorem customRewrite : helper = replacement := rfl
'''
        with self.assertRaisesRegex(ChildProcessError, "custom csimp rewrite"):
            self.audit_property(source)

    def test_transport_requires_executable_source_without_runtime_override(self):
        for label, declaration, diagnostic in [
            ("noncomputable", 'noncomputable def decode (j : Lean.Json) : Except String Nat := Lean.fromJson? j', "safe and executable"),
            ("unsafe", 'unsafe def decode (j : Lean.Json) : Except String Nat := Lean.fromJson? j', "safe and executable"),
            ("override", '''def wrong (_ : Lean.Json) : Except String Nat := .ok 0
@[implemented_by wrong] def decode (j : Lean.Json) : Except String Nat := Lean.fromJson? j''', "runtime implementation override"),
            ("extern", '@[extern "forged_decode"] def decode (j : Lean.Json) : Except String Nat := Lean.fromJson? j', "runtime implementation override"),
        ]:
            with self.subTest(case=label):
                with self.assertRaisesRegex(ChildProcessError, diagnostic):
                    self.audit_transport(f"import Lean\nnamespace Transport\n{declaration}\nend Transport\n")

    def test_transport_accepts_frozen_json_parser_wrapper(self):
        self.audit_transport('''import Lean
namespace Transport
def decode (text : String) : Except String Lean.Json := Lean.Json.parse text
end Transport
''')

    def test_executable_audit_follows_helper_implementations(self):
        source = GOOD.replace(
            "def check (i : View.Input) (o : View.Observation) : Bool := decide (o = i)",
            '''def wrong (_ : View.Input) (_ : View.Observation) : Bool := false
@[implemented_by wrong] def helper (i : View.Input) (o : View.Observation) : Bool := decide (o = i)
def check (i : View.Input) (o : View.Observation) : Bool := helper i o''',
        )
        with self.assertRaisesRegex(ChildProcessError, "runtime implementation override"):
            self.audit_property(source)


if __name__ == "__main__":
    unittest.main()
