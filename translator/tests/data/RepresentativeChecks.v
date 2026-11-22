From Coq Require Import String List Bool ZArith.
From ALCoq Require Import Values.
From DataFixture Require Import Types_0000.
Import ListNotations.
Open Scope string_scope.

Definition first_tree := g_fixture_record_tree "root" g_fixture_case_forest_x3a_0.
Definition nested_tree := g_fixture_record_tree "root"
  (g_fixture_case_forest_x3a_1 first_tree g_fixture_case_forest_x3a_0).
Example recursive_record_equality : g_fixture_type_tree_equal nested_tree nested_tree = true.
Proof. reflexivity. Qed.
Example recursive_record_difference : g_fixture_type_tree_equal first_tree nested_tree = false.
Proof. reflexivity. Qed.
Example nested_container_equality :
  g_fixture_type_nested_equal
    (g_fixture_case_nested_x3a_0 ([nested_tree], Some first_tree))
    (g_fixture_case_nested_x3a_0 ([nested_tree], Some first_tree)) = true.
Proof. reflexivity. Qed.

(* Source lexical atom order differs from constructor declaration order. *)
Example source_atom_order :
  g_fixture_type_ordered_compare g_fixture_case_ordered_x3a_0 g_fixture_case_ordered_x3a_1 = Gt.
Proof. reflexivity. Qed.
(* Arguments in the common mixfix prefix are compared before A/B suffixes,
   even though their source static types differ. *)
Example heterogeneous_prefix_order :
  g_fixture_type_mixed_compare
    (g_fixture_case_mixed_x3a_0 (g_fixture_case_narrow_x3a_0 "z"))
    (g_fixture_case_mixed_x3a_1 (g_fixture_case_broad_x3a_0 "a")) = Gt.
Proof. reflexivity. Qed.

Definition independent_capabilities : ValueOps nat :=
  {| equal_value := fun _ _ => false; compare_value := fun _ _ => Eq;
     print_value := fun _ _ => "debug"; unparse_value := fun _ => Some "source" |}.
Example polymorphic_equality_uses_equality :
  g_fixture_type_tagged_equal nat independent_capabilities
    (g_fixture_case_tagged_x3a_0 0) (g_fixture_case_tagged_x3a_0 0) = false.
Proof. reflexivity. Qed.
Example polymorphic_order_uses_order :
  g_fixture_type_tagged_compare nat independent_capabilities
    (g_fixture_case_tagged_x3a_0 0) (g_fixture_case_tagged_x3a_0 7) = Eq.
Proof. reflexivity. Qed.
Example polymorphic_record_containers :
  g_fixture_type_box_equal nat nat_ops
    (g_fixture_record_box 1 [2; 3] (Some 4))
    (g_fixture_record_box 1 [2; 3] (Some 4)) = true.
Proof. reflexivity. Qed.
Example debug_printer_ignores_unparse_hint :
  g_fixture_type_hinted_print 0 (g_fixture_case_hinted_x3a_0 "x") = "MARK x".
Proof. reflexivity. Qed.
Example source_unparser_uses_hint :
  g_fixture_type_hinted_unparse (g_fixture_case_hinted_x3a_0 "x") = Some "!x".
Proof. reflexivity. Qed.
Example unreferenced_hint_argument_is_not_unparsed :
  g_fixture_type_ignoredHint_unparse (g_fixture_case_ignoredHint_x3a_0 first_tree) = Some "ok".
Proof. reflexivity. Qed.
Example unparse_unsupported_record : g_fixture_type_tree_unparse first_tree = None.
Proof. reflexivity. Qed.
Example extern_is_singleton : forall x : g_fixture_type_opaque, x = g_fixture_extern_opaque.
Proof. destruct x; reflexivity. Qed.
Example ordinary_empty_is_empty : forall T (x : g_fixture_type_empty T), False.
Proof. intros T x; destruct x. Qed.
Definition recursive_alias_is_list : g_fixture_type_recursiveChildren := [g_fixture_record_recursive []].
Example recursive_alias_equality :
  g_fixture_type_recursiveChildren_equal recursive_alias_is_list recursive_alias_is_list = true.
Proof. reflexivity. Qed.
Example flat_tuple_print : g_fixture_type_triple_print 0 (1, true, "x") = "(1, true, x)".
Proof. reflexivity. Qed.
Example flat_tuple_unparse : g_fixture_type_triple_unparse (1, true, "x") = Some "(1, true, x)".
Proof. reflexivity. Qed.
(* Num.compare orders numeric representation tags before magnitudes. *)
Example numeric_representation_order :
  g_fixture_type_mixedNumeric_compare
    (g_fixture_case_mixedNumeric_x3a_0 100)
    (g_fixture_case_mixedNumeric_x3a_1 (-1)%Z) = Lt.
Proof. reflexivity. Qed.
Definition nested_poly := g_fixture_case_nestedPoly_x3a_1
  (g_fixture_case_bag_x3a_0 [g_fixture_case_duo_x3a_0 1 g_fixture_case_nestedPoly_x3a_0]).
Example recursive_generic_container_equality :
  g_fixture_type_nestedPoly_equal nested_poly nested_poly = true.
Proof. reflexivity. Qed.
Definition nested_poly_tree := g_fixture_case_nestedPoly_x3a_2
  (g_fixture_case_polyTree_x3a_1 [g_fixture_case_polyTree_x3a_0 nested_poly]).
Example recursive_generic_tree_equality :
  g_fixture_type_nestedPoly_equal nested_poly_tree nested_poly_tree = true.
Proof. reflexivity. Qed.
