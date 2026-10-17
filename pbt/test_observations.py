"""Typed observation selection and real Lean compilation, with no external Python packages."""

import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

from pbt import observations
from pbt.lean_tools import elaborate, rebuild_modules

REPOSITORY = Path(__file__).resolve().parents[1]


def manifest():
    return {
        "schema_version": 1, "namespace": "Fixture",
        "types": {
            "nat": {"kind": "primitive", "lean": "Nat"},
            "inner": {"kind": "record", "lean": "Fixture.Inner", "fields": {
                "value": {"type": "nat", "lean": "renamed"},
                "hidden": {"type": "nat", "lean": "hidden"}}},
            "result": {"kind": "record", "lean": "Fixture.Result", "fields": {
                "inner": {"type": "inner", "lean": "inner"},
                "flag": {"type": "nat", "lean": "flag"}}},
        },
        "relations": {"Eval": {"lean": "Fixture.Eval", "inputs": [2, 0],
            "arguments": [{"type": "nat"}, {"type": "result"},
                          {"type": "nat"}, {"type": "nat"}]},
            "Closed": {"lean": "Fixture.Closed", "inputs": [],
                       "arguments": [{"type": "nat"}]}}
    }


def alias_manifest():
    value = manifest()
    value["types"]["inner_alias"] = {"kind": "alias", "lean": "Fixture.InnerAlias", "type": "inner"}
    value["types"]["result"]["fields"]["inner"]["type"] = "inner_alias"
    value["types"]["result_alias"] = {"kind": "alias", "lean": "Fixture.ResultAlias", "type": "result"}
    value["types"]["result_alias2"] = {"kind": "alias", "lean": "Fixture.ResultAlias2", "type": "result_alias"}
    value["relations"]["Eval"]["arguments"][1]["type"] = "result_alias2"
    return value


def config(selectors=("%1", "%3"), relation="Eval"):
    return {"schema_version": 1, "observations": [
        {"id": "eval", "relation": relation, "observe": list(selectors)}]}


def make_project(project):
    (project / "Fixtures").mkdir()
    shutil.copyfile(REPOSITORY / "lean-toolchain", project / "lean-toolchain")
    (project / "lakefile.toml").write_text(
        'name = "observations_test"\nversion = "0.1.0"\n'
        '[[lean_lib]]\nname = "Fixtures"\n', encoding="utf-8")
    (project / "Fixtures" / "Helper.lean").write_text(
        "def Fixture.helper : Nat := 7\n", encoding="utf-8")
    (project / "Fixtures" / "Spec.lean").write_text(
        "import Lean\nimport Fixtures.Helper\nnamespace Fixture\n"
        "structure Inner where\n  renamed : Nat\n  hidden : Nat\n  deriving Lean.ToJson, Lean.FromJson\n"
        "structure Result where\n  inner : Inner\n  flag : Nat\n  deriving Lean.ToJson, Lean.FromJson\n"
        "def Eval (first : Nat) (result : Result) (second output : Nat) : Prop :=\n"
        "  first = 2 ∧ second = 3 ∧ result.inner.renamed = first + second ∧ output = 9\n"
        "def Closed (output : Nat) : Prop := output = 7\nend Fixture\n", encoding="utf-8")
    (project / "manifest.json").write_text(json.dumps(manifest()), encoding="utf-8")
    write_config(project)


def write_config(project, selectors=("%1", "%3"), relation="Eval"):
    (project / "observations.toml").write_text(
        'schema_version = 1\n[[observations]]\nid = "eval"\nrelation = '
        + json.dumps(relation) + '\nobserve = ' + json.dumps(list(selectors)) + '\n', encoding="utf-8")


def generate(project, namespace="View", filename="View.lean"):
    return observations.generate_view(
        project, project / "manifest.json", project / "observations.toml", "eval",
        "Fixtures.Spec", namespace, project / "Fixtures" / filename, 60)


class ObservationValidationTests(unittest.TestCase):
    def test_opaque_transport_type_allows_whole_value_but_not_field_selection(self):
        value = manifest()
        value["types"]["sequence"] = {"kind": "opaque", "lean": "Fixture.Sequence"}
        value["relations"]["Closed"]["arguments"][0]["type"] = "sequence"
        selected = observations.validate_observation(config(("%0",), "Closed"), "eval", value)
        self.assertEqual(selected.selectors[0].type_key, "sequence")
        with self.assertRaisesRegex(ValueError, "record"):
            observations.validate_observation(config(("%0.head",), "Closed"), "eval", value)

    def test_selectors_are_typed_and_preserve_selected_order(self):
        selected = observations.validate_observation(config(("%3", "%1.inner.value")), "eval", manifest())
        self.assertEqual([item.type_key for item in selected.selectors], ["nat", "nat"])
        self.assertEqual([item.slot for item in selected.selectors], [3, 1])
        self.assertEqual(selected.selectors[1].lean_fields, ("inner", "renamed"))

    def test_alias_chains_resolve_record_fields_and_reject_cycles(self):
        value = alias_manifest()
        selected = observations.validate_observation(config(("%1.inner.value",)), "eval", value)
        self.assertEqual(selected.selectors[0].type_key, "nat")
        self.assertEqual(selected.selectors[0].lean_fields, ("inner", "renamed"))
        invalid = alias_manifest()
        invalid["types"]["result_alias"]["type"] = "result_alias2"
        with self.assertRaisesRegex(ValueError, "alias.*cycle"):
            observations.validate_manifest(invalid)
        invalid = alias_manifest()
        invalid["types"]["result_alias"]["type"] = "unknown"
        with self.assertRaisesRegex(ValueError, "unknown type"):
            observations.validate_manifest(invalid)
        invalid = alias_manifest()
        invalid["types"]["result_alias"]["type"] = "result_alias"
        with self.assertRaisesRegex(ValueError, "alias.*cycle"):
            observations.validate_manifest(invalid)

    def test_invalid_observations_fail_with_context(self):
        invalid = [
            (config(relation="Missing"), "relation"),
            (config(("%0",)), "input"), (config(("%2",)), "input"),
            (config(("%4",)), "range"), (config(("%1.missing",)), "field"),
            (config(("%3.value",)), "record"), (config(("%1.inner.missing",)), "field"),
            (config(("%3", "%3")), "overlap"),
            (config(("%1", "%1.inner.value")), "overlap"),
            (config(("%1.inner.value", "%1.inner")), "overlap"),
            (config(()), "empty"), (config(("%01",)), "selector"),
            (config(("%1; #eval 0",)), "selector"),
            ({**config(), "schema_version": True}, "schema"),
            ({**config(), "extra": 1}, "unknown"),
            ({**config(), "observations": config()["observations"] * 2}, "duplicate"),
        ]
        for value, message in invalid:
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, message):
                observations.validate_observation(value, "eval", manifest(), source="settings.toml")
        with self.assertRaisesRegex(ValueError, "settings.toml.*missing"):
            observations.validate_observation(config(), "missing", manifest(), source="settings.toml")

    def test_oversized_selector_keeps_source_context(self):
        with self.assertRaisesRegex(ValueError, "settings.toml.*range"):
            observations.validate_observation(config(("%" + "9" * 5000,)), "eval",
                                              manifest(), source="settings.toml")

    def test_manifest_fails_closed(self):
        cases = []
        for key, value in [("schema_version", 2), ("namespace", "Fixture\n#eval 0"), ("extra", 1)]:
            changed = manifest(); changed[key] = value; cases.append(changed)
        for key, value in [("inputs", [0, 0]), ("inputs", [True]), ("inputs", [9]),
                           ("lean", "Fixture.Eval; #eval 0")]:
            changed = manifest(); changed["relations"]["Eval"][key] = value; cases.append(changed)
        for value in ["Nat → Nat", "Nat\n#eval 0", "if", "_", "²"]:
            changed = manifest(); changed["types"]["nat"]["lean"] = value; cases.append(changed)
        changed = manifest(); changed["types"]["nat"]["kind"] = "function"; cases.append(changed)
        changed = manifest(); changed["types"]["result"]["fields"]["flag"]["type"] = "missing"; cases.append(changed)
        changed = manifest(); changed["types"]["result"]["fields"]["flag"]["lean"] = "inner"; cases.append(changed)
        for value in cases:
            with self.subTest(value=value), self.assertRaisesRegex(ValueError, "manifest.json"):
                observations.validate_manifest(value, source="manifest.json")

    def test_render_revalidates_selector_objects(self):
        selected = observations.validate_observation(config(), "eval", manifest())
        forged = observations.Observation(selected.id, selected.relation,
            (observations.Selector(0, (), (), "nat"),), selected.config)
        with self.assertRaisesRegex(ValueError, "selector"):
            observations.render_view(manifest(), forged, "Fixtures.Spec", "View", "0" * 64)

    def test_json_duplicates_and_toml_parse_errors_have_paths(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory)
            path = project / "manifest.json"
            path.write_text('{"schema_version":1,"schema_version":1}', encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "manifest.json.*duplicate"):
                observations.load_manifest(path)
            path = project / "observations.toml"
            path.write_text('schema_version = [', encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "observations.toml"):
                observations.load_config(path)


class ObservationLeanTests(unittest.TestCase):
    def test_whole_and_partial_views_compile_with_original_relation_positions(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory); make_project(project)
            profile = generate(project)
            write_config(project, ("%3", "%1.inner.value"))
            partial = generate(project, "Partial", "Partial.lean")
            self.assertNotEqual(profile, partial)
            rebuild_modules(project, ["Fixtures.View", "Fixtures.Partial"], 60)
            elaborate(project,
                "import Fixtures.View\nimport Fixtures.Partial\n"
                "example : View.Input = (Nat × Nat) := rfl\n"
                "example : View.FullOutput = (Fixture.Result × Nat) := rfl\n"
                "example : Partial.Observation = (Nat × Nat) := rfl\n"
                "example : View.project (⟨⟨5, 100⟩, 4⟩, 9) = (⟨⟨5, 100⟩, 4⟩, 9) := rfl\n"
                "example : Partial.project (⟨⟨5, 100⟩, 4⟩, 9) = (9, 5) := rfl\n"
                "example : Partial.Specification (2, 3) (9, 5) := by\n"
                "  exact ⟨(⟨⟨5, 100⟩, 4⟩, 9), ⟨rfl, rfl, rfl, rfl⟩, rfl⟩\n"
                "example : ¬ Partial.Specification (3, 2) (9, 5) := by\n"
                "  intro ⟨full, h, _⟩; cases h.1\n", 60)

    def test_three_selected_fields_are_right_associated_and_ignore_hidden_values(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory); make_project(project)
            write_config(project, ("%1.inner.value", "%3", "%1.flag")); generate(project)
            rebuild_modules(project, ["Fixtures.View"], 60)
            elaborate(project,
                "import Fixtures.View\n"
                "example : View.Observation = (Nat × (Nat × Nat)) := rfl\n"
                "example : View.project (⟨⟨5, 100⟩, 4⟩, 9) = (5, (9, 4)) := rfl\n"
                "example : View.project (⟨⟨5, 100⟩, 4⟩, 9) = "
                "View.project (⟨⟨5, 200⟩, 4⟩, 9) := rfl\n", 60)

    def test_alias_record_and_nested_alias_views_compile(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory); make_project(project)
            path = project / "Fixtures" / "Spec.lean"
            path.write_text(path.read_text() + "\nnamespace Fixture\n"
                "abbrev InnerAlias := Inner\nabbrev ResultAlias := Result\n"
                "abbrev ResultAlias2 := ResultAlias\nend Fixture\n", encoding="utf-8")
            (project / "manifest.json").write_text(json.dumps(alias_manifest()), encoding="utf-8")
            write_config(project, ("%1.inner.value",)); generate(project)
            rebuild_modules(project, ["Fixtures.View"], 60)
            elaborate(project,
                "import Fixtures.View\n"
                "example : View.FullOutput = (Fixture.ResultAlias2 × Nat) := rfl\n"
                "example : View.Observation = Nat := rfl\n"
                "example : View.project (⟨⟨5, 100⟩, 4⟩, 9) = 5 := rfl\n", 60)

    def test_transport_helpers_ignore_names_in_selected_namespace(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory); make_project(project)
            path = project / "Fixtures" / "Spec.lean"
            path.write_text(path.read_text() + "\nnamespace View.Lean\n"
                            "abbrev Json := Nat\nend View.Lean\n", encoding="utf-8")
            generate(project)

    def test_transport_helpers_freeze_instances_before_property_imports(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory); make_project(project)
            write_config(project, ("%3",)); generate(project)
            rebuild_modules(project, ["Fixtures.View"], 60)
            result = elaborate(project,
                "import Fixtures.View\n"
                "instance (priority := 9999) : Lean.FromJson Nat where\n"
                "  fromJson? _ := .ok 99\n"
                "instance (priority := 9999) : Lean.ToJson Nat where\n"
                "  toJson _ := .null\n"
                "#eval match View.decodeObservation (.num 7) with\n"
                "  | .ok value => value == 7\n  | .error _ => false\n"
                "#eval (View.encodeInput (2, 3)).compress\n"
                "#eval match View.decodeInput (.arr #[.num 2, .num 3]) with\n"
                "  | .ok (first, second) => first == 2 && second == 3\n  | .error _ => false\n", 60)
            self.assertEqual(result.splitlines(), ["true", '"[2,3]"', "true"])

    def test_zero_inputs_and_single_observation_use_unit_and_unwrapped_type(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory); make_project(project)
            write_config(project, ("%0",), "Closed"); generate(project)
            rebuild_modules(project, ["Fixtures.View"], 60)
            elaborate(project,
                "import Fixtures.View\nexample : View.Input = Unit := rfl\n"
                "example : View.Observation = Nat := rfl\n"
                "example : View.FullOutput = Nat := rfl\n"
                "example : View.project 7 = 7 := rfl\n"
                "example : View.Specification () 7 := ⟨7, rfl, rfl⟩\n", 60)

    def test_compile_failure_and_existing_destination_never_publish(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory); make_project(project)
            value = manifest(); value["relations"]["Eval"]["lean"] = "Fixture.DoesNotExist"
            (project / "manifest.json").write_text(json.dumps(value), encoding="utf-8")
            with self.assertRaises(ChildProcessError): generate(project)
            self.assertFalse((project / "Fixtures" / "View.lean").exists())
            (project / "manifest.json").write_text(json.dumps(manifest()), encoding="utf-8")
            generate(project)
            before = (project / "Fixtures" / "View.lean").read_bytes()
            with self.assertRaises(FileExistsError): generate(project)
            self.assertEqual((project / "Fixtures" / "View.lean").read_bytes(), before)

    def test_source_fingerprint_keys_are_portable_across_toolchain_locations(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory); make_project(project)
            rebuild_modules(project, ["Fixtures.Spec"], 60)
            files = observations._source_fingerprints(project, "Fixtures.Spec", 60)
            self.assertIn("Fixtures/Spec.lean", files)
            self.assertIn("Fixtures/Helper.lean", files)
            self.assertTrue(any(key.startswith("lean-toolchain:/src/lean/") for key in files))
            self.assertFalse(any(Path(key).is_absolute() for key in files))

    def test_profile_tracks_manifest_selected_config_spec_and_imported_sources(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory); make_project(project)
            original = generate(project)
            args = (project, project / "manifest.json", project / "observations.toml", "eval", "Fixtures.Spec")
            self.assertEqual(observations.recompute_profile_id(*args), original)
            helper = project / "Fixtures" / "Helper.lean"
            helper.write_text("def Fixture.helper : Nat := 8\n", encoding="utf-8")
            self.assertNotEqual(observations.recompute_profile_id(*args), original)
            helper.write_text("def Fixture.helper : Nat := 7\n", encoding="utf-8")
            spec = project / "Fixtures" / "Spec.lean"
            spec_original = spec.read_text()
            spec.write_text(spec_original + "\n-- semantic revision\n", encoding="utf-8")
            self.assertNotEqual(observations.recompute_profile_id(*args), original)
            spec.write_text(spec_original, encoding="utf-8")
            changed_manifest = manifest()
            changed_manifest["types"]["unused"] = {"kind": "primitive", "lean": "Int"}
            (project / "manifest.json").write_text(json.dumps(changed_manifest), encoding="utf-8")
            self.assertNotEqual(observations.recompute_profile_id(*args), original)
            (project / "manifest.json").write_text(json.dumps(manifest()), encoding="utf-8")
            self.assertEqual(observations.recompute_profile_id(*args), original)
            write_config(project, ("%3", "%1"))
            self.assertNotEqual(observations.recompute_profile_id(*args), original)

    def test_generated_view_validation_rejects_edits_retaining_profile_id(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory); make_project(project)
            original = generate(project)
            args = (project, project / "manifest.json", project / "observations.toml", "eval",
                    "Fixtures.Spec", "Fixtures.View", "View", 60)
            self.assertEqual(observations.validate_generated_view(*args), original)
            path = project / "Fixtures" / "View.lean"
            before = path.read_text()
            altered = before.replace("  ((full).1, (full).2)", "  ((full).1, ((full).2 + 1))")
            self.assertNotEqual(altered, before)
            self.assertIn(original, altered)
            path.write_text(altered, encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "generated view"):
                observations.validate_generated_view(*args)

    def test_cli_generates_and_rejects_injection(self):
        with tempfile.TemporaryDirectory() as directory:
            project = Path(directory); make_project(project)
            command = [sys.executable, "-m", "pbt.observations", "--manifest", str(project / "manifest.json"),
                "--config", str(project / "observations.toml"), "--observation", "eval",
                "--spec-module", "Fixtures.Spec", "--namespace", "View", "--project", str(project),
                "--output", str(project / "Fixtures" / "View.lean")]
            result = subprocess.run(command, cwd=REPOSITORY, capture_output=True, text=True, timeout=120)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            command[command.index("View")] = "Injected\n#eval 0"
            result = subprocess.run(command, cwd=REPOSITORY, capture_output=True, text=True, timeout=120)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("identifier", result.stderr)


if __name__ == "__main__":
    unittest.main()
