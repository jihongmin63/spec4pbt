"""Derivation-copy rewrite: version-unique relation names and the literal entity list."""

import unittest

from scripts.cedar import derivation
from scripts.cedar.derivation import (ENTITY_NAMES_LITERAL, RewriteError, declared_names,
                                      reachable_relations, rewrite_candidate, verify_rewrite)

V001 = '''Require Import List.
Require Import Specification.cedar.Spec.
Require Import Property.Original.
(* predicate in a comment and "predicate" in a string stay unchanged *)
Inductive Helper : CedarType -> Prop :=
  | HelperInt : Helper intType
with Other : CedarType -> Prop :=
  | OtherBool : forall b, Helper intType -> Other (boolType b).
Inductive predicate : Original.Input -> Prop :=
  | Base : forall i ty,
      WfCedarType Original.entity_names ty ->
      Helper ty ->
      predicate i.
'''

V002 = '''Require Import List.
Require Import Property.Original.
Require Import Property.candidates.v001.Candidate.
Inductive predicate : Original.Input -> Prop :=
  | Fresh : forall i,
      Property.candidates.v001.Candidate.Helper intType ->
      predicate i
  | Previous : forall i,
      Property.candidates.v001.Candidate.predicate i -> predicate i.
'''


def declared(*sources):
    return {f"v{index:03d}": declared_names(source)
            for index, source in enumerate(sources, 1)}


class RewriteTests(unittest.TestCase):
    def test_declared_names_cover_mutual_inductives_and_constructors(self):
        self.assertEqual(declared_names(V001),
                         ["Helper", "HelperInt", "Other", "OtherBool", "predicate", "Base"])

    def test_rewrite_renames_own_and_predecessor_names_and_entity_list(self):
        names = declared(V001, V002)
        first, changes = rewrite_candidate(V001, "v001", names)
        self.assertIn("Inductive predicate_v001 : Original.Input -> Prop", first)
        self.assertIn("| OtherBool_v001 : forall b, Helper_v001 intType", first)
        self.assertIn(f"WfCedarType {ENTITY_NAMES_LITERAL} ty", first)
        self.assertIn('(* predicate in a comment and "predicate" in a string', first)
        self.assertNotIn("entity_names", first)
        self.assertIn({"line": 11, "from": "Original.entity_names", "to": ENTITY_NAMES_LITERAL},
                      changes)
        verify_rewrite(V001, first, "v001", names)
        second, _ = rewrite_candidate(V002, "v002", names)
        self.assertIn("Property.candidates.v001.Candidate.predicate_v001 i -> predicate_v002 i",
                      second)
        self.assertIn("Property.candidates.v001.Candidate.Helper_v001 intType", second)
        verify_rewrite(V002, second, "v002", names)

    def test_verification_rejects_any_other_change(self):
        names = declared(V001)
        good, _ = rewrite_candidate(V001, "v001", names)
        for bad in (good.replace("intType", "stringType", 1),
                    good.replace("Helper_v001 ty", "Helper ty"),
                    good.replace(ENTITY_NAMES_LITERAL, "Original.entity_names"),
                    good.replace("predicate_v001", "predicate_v002", 1),
                    good.replace(":=", ":= ", 1).replace("|", "", 1)):
            with self.assertRaises(RewriteError):
                verify_rewrite(V001, bad, "v001", names)

    def test_ambiguous_or_partial_references_fail_closed(self):
        unqualified = V002.replace("Property.candidates.v001.Candidate.Helper", "Helper")
        with self.assertRaisesRegex(RewriteError, "unqualified"):
            rewrite_candidate(unqualified, "v002", declared(V001, unqualified))
        partial = V002.replace("Property.candidates.v001.Candidate.predicate",
                               "Candidate.predicate")
        with self.assertRaisesRegex(RewriteError, "partially qualified"):
            rewrite_candidate(partial, "v002", declared(V001, partial))
        later = V001.replace("Helper ty", "Property.candidates.v002.Candidate.predicate i")
        with self.assertRaisesRegex(RewriteError, "non-predecessor"):
            rewrite_candidate(later, "v001", declared(later, V002))

    def test_existing_generated_name_is_a_collision(self):
        colliding = V001.replace("Helper ty ->", "Helper ty -> Helper_v001 ty ->")
        with self.assertRaisesRegex(RewriteError, "collides"):
            rewrite_candidate(colliding, "v001", declared(colliding))

    def test_reachability_follows_premises_not_file_order(self):
        names = declared(V001, V002)
        rewritten = {version: rewrite_candidate(source, version, names)[0]
                     for version, source in (("v001", V001), ("v002", V002))}
        self.assertEqual(reachable_relations(rewritten, "v002"),
                         ["Helper_v001", "predicate_v001", "predicate_v002"])
        standalone = V002.replace(
            "\n  | Previous : forall i,\n      Property.candidates.v001.Candidate.predicate i -> predicate i", "")
        names = declared(V001, standalone)
        rewritten["v002"] = rewrite_candidate(standalone, "v002", names)[0]
        self.assertEqual(reachable_relations(rewritten, "v002"),
                         ["Helper_v001", "predicate_v002"])

    def test_entity_literal_uses_constructors_only(self):
        self.assertTrue(derivation.coq_string("E").startswith(
            "(Coq.Strings.String.String (Coq.Strings.Ascii.Ascii Coq.Init.Datatypes.true "
            "Coq.Init.Datatypes.false Coq.Init.Datatypes.true Coq.Init.Datatypes.false"))
        self.assertNotIn('"', ENTITY_NAMES_LITERAL)
        self.assertNotIn("%", ENTITY_NAMES_LITERAL)


if __name__ == "__main__":
    unittest.main()
