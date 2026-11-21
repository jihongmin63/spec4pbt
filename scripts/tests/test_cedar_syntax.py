#!/usr/bin/env python3
"""Real Coq regressions for the pre-prover Cedar syntax gate."""

import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[2]
PROPERTY = ROOT / "properties/cedar_no_type_error"
ENV = ROOT / "environment/env.sh"
GATE = ROOT / "scripts/cedar/syntax.py"
sys.path.insert(0, str(ROOT))
from scripts.cedar.syntax import peel_foralls


class CedarSyntaxTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        (PROPERTY / ".runs").mkdir(parents=True, exist_ok=True)
        cls.root = Path(tempfile.mkdtemp(prefix="syntax-test-", dir=PROPERTY / ".runs"))
        cls.property = cls.root / "property"
        (cls.property / "candidates/v001").mkdir(parents=True)
        shutil.copy2(PROPERTY / "Original.v", cls.property / "Original.v")

    def gate(self, label, candidate, success, fragment=None, expect_compiled=True):
        (self.property / "candidates/v001/Candidate.v").write_text(candidate)
        evidence = self.root / label
        command = [sys.executable, str(GATE), str(self.property), "--candidate", "v001",
                   "--evidence-dir", str(evidence), "--env-script", str(ENV)]
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=120)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        report = json.loads((evidence / "result.json").read_text())
        self.assertEqual(report["status"], "passed" if success else "failed")
        if fragment:
            self.assertIn(fragment, report.get("error", ""))
        if expect_compiled and label not in {"malformed", "changed-original"}:
            self.assertTrue(any(item["command"][-1] == "property/candidates/v001/Candidate.v"
                                for item in report["commands"]))
        return command, report

    def gate_prefix(self, label, sources, success, fragment=None):
        staged = self.root / (label + "-property")
        staged.mkdir()
        shutil.copy2(PROPERTY / "Original.v", staged / "Original.v")
        for index, source in enumerate(sources, 1):
            candidate = staged / f"candidates/v{index:03d}/Candidate.v"
            candidate.parent.mkdir(parents=True, exist_ok=True)
            candidate.write_text(source)
        evidence = self.root / label
        result = subprocess.run([sys.executable, str(GATE), str(staged),
                                 "--candidate", f"v{len(sources):03d}",
                                 "--evidence-dir", str(evidence),
                                 "--env-script", str(ENV)], cwd=ROOT, text=True,
                                capture_output=True, timeout=120)
        self.assertEqual(result.returncode == 0, success, result.stdout + result.stderr)
        report = json.loads((evidence / "result.json").read_text())
        self.assertEqual(report["status"], "passed" if success else "failed")
        if fragment:
            self.assertIn(fragment, report.get("error", ""))
        return report

    def test_peel_foralls_accepts_whitespace_after_keyword(self):
        for separator in (" ", "\n ", "\t", "\r\n  "):
            with self.subTest(separator=repr(separator)):
                binders, result = peel_foralls(
                    f"forall{separator}(x : nat) (y : nat), R x y")
                self.assertEqual(binders, [("x", "nat"), ("y", "nat")])
                self.assertEqual(result, "R x y")
        self.assertEqual(peel_foralls("forallx (x : nat), R x"),
                         ([], "forallx (x : nat), R x"))

    def test_multiple_constructors_with_wrapped_forall(self):
        source = """Require Import Property.Original.
Inductive predicate : Original.Input -> Prop :=
| from_schema : forall
    (entity_entries : list
      (Specification.cedar.Spec.EntityName * Specification.cedar.Spec.EntitySchemaEntry))
    (action_entries : list
      (Specification.cedar.Spec.EntityUID * Specification.cedar.Spec.ActionSchemaEntry))
    (i : Original.Input),
    Specification.cedar.Spec.WfSchema Original.entity_names
      (Specification.cedar.Spec.MkSchema entity_entries action_entries) ->
    predicate i
| from_type : forall (i : Original.Input)
    (w : Specification.cedar.Spec.CedarType),
    Specification.cedar.Spec.WfCedarType Original.entity_names w ->
    predicate i.
"""
        _, report = self.gate("wrapped-forall", source, True)
        self.assertEqual(report["new_relations"], ["predicate"])
        self.assertEqual({item["constructor"] for item in report["binders"]
                          if item["classification"] == "relation premise"},
                         {"from_schema", "from_type"})
        printed = (self.root / "wrapped-forall" / "elaborated-v001.log").read_text()
        self.assertIn("from_schema : forall\n", printed)

    def test_relations_and_fixed_spec_function_premise(self):
        # Spec.WfSchema has dedupActsById acts = acts' in its own constructor.
        # That fixed declaration is exempt; the new premises are applications.
        source = """Require Import Property.Original.
Inductive helper : Original.Input -> Prop :=
| mk_helper : forall i : Original.Input,
    Specification.cedar.Spec.WfSchema Original.entity_names
      (Specification.cedar.Spec.MkSchema (Original.ets i) (Original.acts i)) ->
    helper i
| mk_helper_witness : forall (i : Original.Input)
    (w : Specification.cedar.Spec.CedarType),
    Specification.cedar.Spec.WfCedarType Original.entity_names w -> helper i.
Inductive predicate : Original.Input -> Prop :=
| mk_predicate : forall i : Original.Input, helper i -> predicate i.
"""
        _, report = self.gate("positive", source, True)
        self.assertEqual(report["new_relations"], ["helper", "predicate"])
        self.assertEqual([b["classification"] for b in report["binders"]
                          if b["classification"] == "relation premise"],
                         ["relation premise", "relation premise", "relation premise"])

    def test_boolean_function_premise(self):
        source = """Require Import Property.Original Bool.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    (Bool.eqb true true = true) -> predicate i.
"""
        self.gate("boolean", source, False, "not a permitted inductive relation")

    def test_quickchick_hint_mutation_cannot_change_frozen_support(self):
        source = """Require Import Property.Original.
From QuickChick Require Import QuickChick.
#[global] Remove Hints genBoolSized : typeclass_instances.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i) ->
    predicate i.
"""
        self.gate("quickchick-hint", source, False, "candidate import", expect_compiled=False)

    def test_policy_and_proof_commands_rejected_independently(self):
        commands = {
            "hint": "Hint Resolve I : core.",
            "remove-hints": "#[global] Remove Hints genBoolSized : typeclass_instances.",
            "existing-instance": "Existing Instance genBoolSized.",
            "instance": "Instance custom_gen : True := I.",
            "option": "Set Universe Polymorphism.",
            "automation": "Ltac automate := idtac.",
        }
        for label, command in commands.items():
            with self.subTest(command=label):
                source = """Require Import Property.Original.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i) ->
    predicate i.
""" + command + "\n"
                self.gate("policy-" + label, source, False,
                          "candidate command", expect_compiled=False)

    def test_standard_data_notation_import_is_allowed(self):
        source = """From Coq Require Import Lists.List.
Require Import Property.Original.
Import ListNotations.
Open Scope list_scope.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i) ->
    predicate i.
"""
        self.gate("data-notation", source, True)

    def test_definition_wrapper(self):
        source = """Require Import Property.Original.
Definition wrapped (i : Original.Input) : Prop :=
  Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i).
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input, wrapped i -> predicate i.
"""
        self.gate("wrapper", source, False, "candidate command", expect_compiled=False)

    def test_inductive_wrapper_cannot_hide_boolean_premise(self):
        source = """Require Import Property.Original Bool.
Inductive helper : Original.Input -> Prop :=
| mk_helper : forall i : Original.Input,
    (Bool.eqb true true = true) -> helper i.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input, helper i -> predicate i.
"""
        self.gate("inductive-wrapper", source, False, "not a permitted inductive relation")

    def test_nested_forall(self):
        source = """Require Import Property.Original.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    (forall j : Original.Input,
      Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty j)) ->
    predicate i.
"""
        self.gate("nested-forall", source, False, "higher-order or nested")

    def test_if_in_premise(self):
        source = """Require Import Property.Original.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    (if true then
      Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i)
     else
      Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i)) ->
    predicate i.
"""
        self.gate("if-premise", source, False, "higher-order or nested")

    def test_match_in_premise(self):
        source = """Require Import Property.Original.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    (match true with
     | true => Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i)
     | false => Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i)
     end) -> predicate i.
"""
        self.gate("match-premise", source, False, "higher-order or nested")

    def test_improper_type(self):
        source = """Require Import Property.Original.
Inductive predicate : nat -> Prop :=
| mk : predicate 0.
"""
        self.gate("wrong-type", source, False, "elaborated-v001 failed")

    def test_malformed_coq(self):
        source = """Require Import Property.Original.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input, predicate i
"""
        self.gate("malformed", source, False, "Unterminated candidate command",
                  expect_compiled=False)

    def test_evidence_cannot_be_overwritten(self):
        source = """Require Import Property.Original.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i) ->
    predicate i.
"""
        command, _ = self.gate("immutable", source, True)
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True, timeout=120)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("File exists", result.stderr)

    def test_staged_original_must_be_fixed(self):
        source = """Require Import Property.Original.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i) ->
    predicate i.
"""
        original = self.property / "Original.v"
        original.write_text(original.read_text() + "\n(* changed *)\n")
        try:
            self.gate("changed-original", source, False, "differs from the fixed")
        finally:
            shutil.copy2(PROPERTY / "Original.v", original)

    def test_v002_uses_predecessor_without_equivalence_file(self):
        previous = """Require Import Property.Original.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i) ->
    predicate i.
"""
        current = """Require Import Property.candidates.v001.Candidate.
Inductive predicate : Property.Original.Input -> Prop :=
| mk : forall i : Property.Original.Input,
    Property.candidates.v001.Candidate.predicate i -> predicate i.
"""
        (self.property / "candidates/v001/Candidate.v").write_text(previous)
        v002 = self.property / "candidates/v002"
        v002.mkdir(exist_ok=True)
        (v002 / "Candidate.v").write_text(current)
        self.assertFalse((self.property / "candidates/v001/Equivalence.v").exists())
        self.assertFalse((v002 / "Equivalence.v").exists())
        evidence = self.root / "v002"
        result = subprocess.run([sys.executable, str(GATE), str(self.property),
                                 "--candidate", "v002", "--evidence-dir", str(evidence),
                                 "--env-script", str(ENV)], cwd=ROOT, text=True,
                                capture_output=True, timeout=120)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        report = json.loads((evidence / "result.json").read_text())
        self.assertEqual(report["verified_relations"],
                         {"v001": ["predicate"], "v002": ["predicate"]})

    def test_prior_helper_printed_as_candidate_alias_is_accepted(self):
        previous = """Require Import Property.Original.
Inductive SeedSchema : Original.Input -> Prop :=
| seed : forall i : Original.Input,
    Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i) ->
    SeedSchema i.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input, SeedSchema i -> predicate i.
"""
        current = """Require Import Property.candidates.v001.Candidate.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    Property.candidates.v001.Candidate.SeedSchema i -> predicate i.
"""
        report = self.gate_prefix("prior-helper-alias", [previous, current], True)
        printed = (self.root / "prior-helper-alias/elaborated-v002.log").read_text()
        self.assertIn("Candidate.SeedSchema i", printed)
        premises = [binder for binder in report["binders"]
                    if binder["version"] == "v002" and
                    binder["classification"] == "relation premise"]
        self.assertEqual(len(premises), 1)

    def test_same_helper_name_in_multiple_prior_modules_and_current(self):
        first = """Require Import Property.Original.
Inductive Shared : Original.Input -> Prop :=
| one : forall i : Original.Input,
    Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i) ->
    Shared i.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input, Shared i -> predicate i.
"""
        second = """Require Import Property.candidates.v001.Candidate.
Inductive Shared : Original.Input -> Prop :=
| two : forall i : Original.Input,
    Property.candidates.v001.Candidate.Shared i -> Shared i.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input, Shared i -> predicate i.
"""
        third = """Require Import Property.candidates.v001.Candidate.
Require Import Property.candidates.v002.Candidate.
Inductive Shared : Original.Input -> Prop :=
| three : forall i : Original.Input,
    Property.candidates.v001.Candidate.Shared i ->
    Property.candidates.v002.Candidate.Shared i -> Shared i.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input,
    Property.candidates.v001.Candidate.Shared i ->
    Property.candidates.v002.Candidate.Shared i ->
    Shared i -> predicate i.
"""
        report = self.gate_prefix("colliding-helper-aliases", [first, second, third], True)
        premises = [binder for binder in report["binders"]
                    if binder["version"] == "v003" and
                    binder["classification"] == "relation premise"]
        self.assertEqual(len(premises), 5)
        self.assertEqual(sorted(binder["resolved_relation"] for binder in premises),
                         sorted([
                             "Property.candidates.v001.Candidate.Shared",
                             "Property.candidates.v001.Candidate.Shared",
                             "Property.candidates.v002.Candidate.Shared",
                             "Property.candidates.v002.Candidate.Shared",
                             "Property.candidates.v003.Candidate.Shared",
                         ]))

    def test_local_type_binder_shadowing_relation_name_is_data(self):
        source = """Require Import Property.Original.
Inductive Shared : Original.Input -> Prop :=
| base : forall i : Original.Input,
    Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i) ->
    Shared i.
Inductive predicate : Original.Input -> Prop :=
| mk : forall (Shared : Set) (x : Shared) (i : Original.Input),
    Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i) ->
    predicate i.
"""
        report = self.gate_prefix("local-type-shadow", [source], True)
        binder = next(b for b in report["binders"]
                      if b["constructor"] == "mk" and b["type"] == "Shared")
        self.assertEqual(binder["classification"], "data binder")

    def test_original_prop_function_is_not_a_relation(self):
        source = """Require Import Property.Original.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input, Original.predicate i -> predicate i.
"""
        self.gate_prefix("original-function", [source], False,
                         "not a permitted inductive relation")

    def test_inductive_wrapper_cannot_hide_original_prop_function(self):
        source = """Require Import Property.Original.
Inductive Shared : Original.Input -> Prop :=
| wrap : forall i : Original.Input, Original.predicate i -> Shared i.
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input, Shared i -> predicate i.
"""
        self.gate_prefix("original-function-wrapper", [source], False,
                         "not a permitted inductive relation")


if __name__ == "__main__":
    unittest.main()
