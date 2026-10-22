"""Real donor IL metadata, raw translation, and native JSON transport."""

import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from pbt.observations import validate_manifest, validate_observation
from translator.toolchain import metadata_executable, resolve_toolchain


from tests import ROOT, FIXTURES, ORDERED, SCRATCH


def config(relation, *selectors):
    return {"schema_version": 1, "observations": [
        {"id": "value", "relation": relation, "observe": list(selectors)}]}


def run(command, *, cwd=None, env=None):
    return subprocess.run(command, cwd=cwd, env=env, text=True,
                          capture_output=True, timeout=90)


class MetadataTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix="p4-metadata-tests-", dir=SCRATCH)
        cls.addClassCleanup(cls.directory.cleanup)
        cls.build = Path(cls.directory.name)
        cls.tool = resolve_toolchain(ROOT)
        cls.helper = metadata_executable(ROOT, cls.tool)

    def helper_result(self, fixture, configuration, model=None):
        self.assertTrue(self.helper.is_file(), "typed donor metadata helper is not implemented")
        settings = self.build / "config.json"
        settings.write_text(json.dumps(configuration))
        optional = ["--transport-model", str(FIXTURES / model)] if model else []
        return run([str(self.helper), "--spec-module", "Spec", "--namespace", "Transport",
                    "--config", str(settings), *optional, str(FIXTURES / fixture)])

    def metadata(self, fixture, configuration, model=None):
        result = self.helper_result(fixture, configuration, model)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        value = json.loads(result.stdout)
        self.assertEqual(set(value), {"manifest", "transport"})
        validate_manifest(value["manifest"])
        validate_observation(configuration, "value", value["manifest"])
        return value

    def compile(self, fixture, configuration, extra="", *, model=None, transport_error=False):
        value = self.metadata(fixture, configuration, model)
        directory = tempfile.TemporaryDirectory(prefix="lean-", dir=self.build)
        self.addCleanup(directory.cleanup)
        project = Path(directory.name)
        shutil.copyfile(ROOT / "lean-toolchain", project / "lean-toolchain")
        (project / "lakefile.toml").write_text(
            'name = "metadata_test"\nversion = "0.1.0"\n'
            '[[lean_lib]]\nname = "Spec"\n'
            '[[lean_lib]]\nname = "Transport"\n')
        translated = run([str(self.tool.executable), str(FIXTURES / fixture)])
        self.assertEqual(translated.returncode, 0, translated.stdout + translated.stderr)
        (project / "Spec.lean").write_text(translated.stdout)
        (project / "Transport.lean").write_text(value["transport"])
        built = run(["lake", "build", "Transport"], cwd=project)
        if transport_error:
            self.assertNotEqual(built.returncode, 0, "missing external codecs unexpectedly compiled")
            self.assertIn("Json", built.stdout + built.stderr)
            return project, value
        self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
        if extra:
            if callable(extra):
                extra = extra(value["manifest"])
            (project / "Check.lean").write_text("import Transport\n" + extra)
            checked = run(["lake", "env", "lean", "--run", "Check.lean"], cwd=project)
            self.assertEqual(checked.returncode, 0, checked.stdout + checked.stderr)
        return project, value

    def test_partial_record_preserves_noncontiguous_input_slots_without_hidden_codecs(self):
        project, value = self.compile("record.watsup", config("Eval", "%1.VALUE", "%3"), '''
example : ({ VALUE := 9, TRACE := .HIDDEN 7 } : SpecTec.result).VALUE = 9 := rfl
def main : IO Unit := do
  let input := ((7, 2) : Nat × Nat)
  let .ok decoded := Lean.fromJson? (α := Nat × Nat) (Lean.toJson input)
    | throw (IO.userError "input codec")
  if decoded != input then throw (IO.userError "input roundtrip")
''')
        self.assertEqual(value["manifest"]["relations"]["Eval"]["inputs"], [0, 2])
        selected = validate_observation(config("Eval", "%1.VALUE", "%3"), "value", value["manifest"])
        self.assertEqual([item.slot for item in selected.selectors], [1, 3])
        self.assertEqual([item.type_key for item in selected.selectors], ["nat", "nat"])
        (project / "Hidden.lean").write_text("import Transport\n#synth Lean.FromJson SpecTec.hidden\n")
        hidden = run(["lake", "env", "lean", "Hidden.lean"], cwd=project)
        self.assertNotEqual(hidden.returncode, 0, "hidden output unexpectedly requires/provides codecs")
        self.assertIn("FromJson", hidden.stdout + hidden.stderr)

    def test_composite_record_roundtrip(self):
        self.compile("composite.watsup", config("Copy", "%1"), '''
def main : IO Unit := do
  let input : SpecTec.payload := { VALUES := [1, 2], MAYBE := some 3, PAIR := (4, "x") }
  let encoded := Lean.toJson input
  let .ok decoded := Lean.fromJson? (α := SpecTec.payload) encoded | throw (IO.userError "decode")
  if decoded.VALUES != [1, 2] || decoded.MAYBE != some 3 || decoded.PAIR != (4, "x") then
    throw (IO.userError "roundtrip changed composite values")
''')

    def test_recursive_variant_roundtrip(self):
        self.compile("recursive.watsup", config("Copy", "%1"), '''
def main : IO Unit := do
  let input : SpecTec.tree := .NODE (.LEAF 1) (.LEAF 2)
  let encoded := Lean.toJson input
  let .ok decoded := Lean.fromJson? (α := SpecTec.tree) encoded | throw (IO.userError "decode")
  if Lean.toJson decoded != encoded then throw (IO.userError "recursive roundtrip")
''')

    def test_closed_generic_alias_with_composite_arguments_roundtrip(self):
        self.compile("generic.watsup", config("Copy", "%1"), '''
def main : IO Unit := do
  let input : SpecTec.packed := .BOX ([1, 2], some 3)
  let encoded := Lean.toJson input
  let .ok decoded := Lean.fromJson? (α := SpecTec.packed) encoded | throw (IO.userError "decode")
  if Lean.toJson decoded != encoded then throw (IO.userError "generic roundtrip")
''')

    def test_nested_alias_field_projection_uses_original_fields(self):
        _, value = self.compile("nested.watsup", config("Get", "%1.INNER.VALUE"), '''
example : ({ INNER := { VALUE := 42, KEEP := 9 }, TRACE := "hidden" } : SpecTec.outer).INNER.VALUE = 42 := rfl
def main : IO Unit := do
  let .ok result := Lean.fromJson? (α := Nat) (Lean.toJson (42 : Nat)) | throw (IO.userError "decode")
  if result != 42 then throw (IO.userError "nested field codec")
''')
        selected = validate_observation(config("Get", "%1.INNER.VALUE"), "value", value["manifest"])
        self.assertEqual(selected.selectors[0].lean_fields, ("INNER", "VALUE"))
        self.assertEqual(selected.selectors[0].type_key, "nat")

    def test_mutually_recursive_data_roundtrip(self):
        self.compile("mutual.watsup", config("Copy", "%1"), '''
def main : IO Unit := do
  let input : SpecTec.node := .NEXT (.BRANCH (.LEAF 8))
  let encoded := Lean.toJson input
  let .ok decoded := Lean.fromJson? (α := SpecTec.node) encoded | throw (IO.userError "decode")
  if Lean.toJson decoded != encoded then throw (IO.userError "mutual roundtrip")
''')

    def test_donor_keyword_names_are_exposed_through_safe_aliases(self):
        self.compile("quoted.watsup", config("Prop", "%1"), lambda manifest: f'''
def main : IO Unit := do
  let input : {manifest["types"]["Type"]["lean"]} := .BOX 11
  let encoded := Lean.toJson input
  let .ok decoded := Lean.fromJson? (α := {manifest["types"]["Type"]["lean"]}) encoded
    | throw (IO.userError "decode")
  if Lean.toJson decoded != encoded then throw (IO.userError "quoted name roundtrip")
''')

    def test_all_profiles_contribute_their_codec_requirements(self):
        configuration = config("Eval", "%1.VALUE")
        configuration["observations"].append({"id": "whole", "relation": "Eval", "observe": ["%1"]})
        self.compile("record.watsup", configuration, '''
#synth Lean.FromJson SpecTec.result
#synth Lean.FromJson SpecTec.hidden
def main : IO Unit := pure ()
''')

    def test_invalid_selectors_and_unknown_relations_fail_before_transport(self):
        for configuration in [config("Missing", "%1"), config("Eval", "%0"),
                              config("Eval", "%1.MISSING"), config("Eval", "%1", "%1.VALUE")]:
            with self.subTest(configuration=configuration):
                result = self.helper_result("record.watsup", configuration)
                self.assertNotEqual(result.returncode, 0)
                self.assertEqual(result.stdout, "")
                self.assertTrue(result.stderr.strip())

    def test_abstract_external_types_are_explicitly_rejected(self):
        result = self.helper_result("extern.watsup", config("Copy", "%1"))
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(result.stdout, "")
        self.assertIn("external", result.stderr.lower())

    def test_user_external_model_freezes_concrete_type_in_transport_alias(self):
        self.compile("extern.watsup", config("Copy", "%1"), lambda manifest: f'''
example : {manifest["types"]["archState"]["lean"]} = Nat := rfl
def main : IO Unit := do
  let input : {manifest["types"]["archState"]["lean"]} := (42 : Nat)
  let .ok decoded := Lean.fromJson? (α := {manifest["types"]["archState"]["lean"]}) (Lean.toJson input)
    | throw (IO.userError "decode")
  if !(Nat.beq decoded 42) then throw (IO.userError "external roundtrip")
''', model="external-nat-model.lean")

    def test_missing_external_codec_is_rejected_by_transport_compilation(self):
        self.compile("extern.watsup", config("Copy", "%1"),
                     model="external-missing-codec-model.lean", transport_error=True)

    def test_external_dependent_record_uses_explicit_model_codecs(self):
        self.compile("extern-record.watsup", config("Copy", "%1"), '''
attribute [local instance] Transport.concrete
def main : IO Unit := do
  let input : SpecTec.payload := { STATE := (9 : Nat), VALUE := 7 }
  let encoded := Lean.toJson input
  let .ok decoded := Lean.fromJson? (α := SpecTec.payload) encoded | throw (IO.userError "decode")
  if !(Nat.beq decoded.STATE 9) || decoded.VALUE != 7 then throw (IO.userError "external record codec")
''', model="external-record-model.lean")

    def test_external_relation_uses_donor_public_typed_declaration(self):
        self.compile("extern-relation.watsup", config("Native", "%1"), lambda manifest: f'''
example : {manifest["relations"]["Native"]["lean"]} 4 99 := by constructor
def main : IO Unit := pure ()
''')


if __name__ == "__main__":
    unittest.main()
