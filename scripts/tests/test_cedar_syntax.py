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


class CedarSyntaxTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.root = Path(tempfile.mkdtemp(prefix="syntax-test-", dir=PROPERTY / ".runs"))
        cls.property = cls.root / "property"
        (cls.property / "candidates/v001").mkdir(parents=True)
        shutil.copy2(PROPERTY / "Original.v", cls.property / "Original.v")

    def gate(self, label, candidate, success, fragment=None):
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
        if label not in {"malformed", "changed-original"}:
            self.assertTrue(any(item["command"][-1] == "property/candidates/v001/Candidate.v"
                                for item in report["commands"]))
        return command, report

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

    def test_definition_wrapper(self):
        source = """Require Import Property.Original.
Definition wrapped (i : Original.Input) : Prop :=
  Specification.cedar.Spec.WfCedarType Original.entity_names (Original.ty i).
Inductive predicate : Original.Input -> Prop :=
| mk : forall i : Original.Input, wrapped i -> predicate i.
"""
        self.gate("wrapper", source, False, "unsupported def")

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
        self.gate("malformed", source, False, "dependencies failed")

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


if __name__ == "__main__":
    unittest.main()
