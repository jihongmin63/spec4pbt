"""Typed relation manifest and observation selector validation."""

import unittest

from pbt import observations


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
            (config(("%01",)), "selector"),
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

    def test_success_only_observation_has_no_selectors(self):
        selected = observations.validate_observation(config(()), "eval", manifest())
        self.assertEqual(selected.id, "eval")
        self.assertEqual(selected.relation, "Eval")
        self.assertEqual(selected.selectors, ())
        self.assertEqual(selected.config, config(())["observations"][0])


if __name__ == "__main__":
    unittest.main()
