From Coq Require Import List ZArith.
Require Import Types Casts.
Import ListNotations.
Example cast_nat_int : g_fixture_cast_0 7%nat = Some 7%Z.
Proof. reflexivity. Qed.
Example cast_negative : g_fixture_cast_1 (-1)%Z = None.
Proof. reflexivity. Qed.
Example cast_zero : g_fixture_cast_1 0%Z = Some 0%nat.
Proof. reflexivity. Qed.
Example cast_list_success : g_fixture_cast_2 [2%Z;0%Z] = Some [2%nat;0%nat].
Proof. reflexivity. Qed.
Example cast_list_failure : g_fixture_cast_2 [2%Z;(-1)%Z] = None.
Proof. reflexivity. Qed.
Example cast_option_empty : g_fixture_cast_3 None = Some None.
Proof. reflexivity. Qed.
Example cast_option_failure : g_fixture_cast_3 (Some (-1)%Z) = None.
Proof. reflexivity. Qed.
Example cast_tuple : g_fixture_cast_4 (2%nat, Some 3%Z, [4%Z]) =
  Some (2%Z, Some 3%nat, [4%nat]).
Proof. reflexivity. Qed.
Example cast_variant : g_fixture_cast_5 (g_fixture_case_narrow_x3a_0 3%nat) =
  Some (g_fixture_case_broad_x3a_0 3%Z).
Proof. reflexivity. Qed.
Example cast_variant_missing : g_fixture_cast_6 g_fixture_case_broad_x3a_1 = None.
Proof. reflexivity. Qed.
Example cast_variant_field_failure : g_fixture_cast_6 (g_fixture_case_broad_x3a_0 (-1)%Z) = None.
Proof. reflexivity. Qed.
Example cast_alias : g_fixture_cast_7 (g_fixture_case_narrow_x3a_0 1%nat) =
  Some (g_fixture_case_broad_x3a_0 1%Z).
Proof. reflexivity. Qed.
Example cast_recursive : g_fixture_cast_8
  (g_fixture_case_narrowTree_x3a_1 [g_fixture_case_narrowTree_x3a_2
    (Some (g_fixture_case_narrowTree_x3a_0 3%nat))]) =
  Some (g_fixture_case_broadTree_x3a_1 [g_fixture_case_broadTree_x3a_2
    (Some (g_fixture_case_broadTree_x3a_0 3%Z))]).
Proof. reflexivity. Qed.
Example cast_recursive_failure : g_fixture_cast_9
  (g_fixture_case_broadTree_x3a_1 [g_fixture_case_broadTree_x3a_3]) = None.
Proof. reflexivity. Qed.
Example cast_generic : g_fixture_cast_10 (@g_fixture_case_tagged_x3a_0 nat 4%nat) =
  Some (@g_fixture_case_tagged_x3a_0 Z 4%Z).
Proof. reflexivity. Qed.
Example cast_record_invariant : g_fixture_cast_11 (@g_fixture_record_invariant nat 1%nat) = None.
Proof. reflexivity. Qed.
Example cast_nested_generic : g_fixture_cast_12
  (g_fixture_case_nestedNarrow_x3a_1 (g_fixture_case_bag_x3a_0
    [g_fixture_case_nestedNarrow_x3a_0])) =
  Some (g_fixture_case_nestedBroad_x3a_1 (g_fixture_case_bag_x3a_0
    [g_fixture_case_nestedBroad_x3a_0])).
Proof. reflexivity. Qed.
Example cast_nested_generic_failure : g_fixture_cast_13
  (g_fixture_case_nestedBroad_x3a_1 (g_fixture_case_bag_x3a_0
    [g_fixture_case_nestedBroad_x3a_2])) = None.
Proof. reflexivity. Qed.
Example cast_mutual : g_fixture_cast_14
  (g_fixture_case_mutualNarrowA_x3a_0 (g_fixture_case_mutualNarrowB_x3a_0 None)) =
  Some (g_fixture_case_mutualBroadA_x3a_0 (g_fixture_case_mutualBroadB_x3a_0 None)).
Proof. reflexivity. Qed.
Example cast_mutual_failure : g_fixture_cast_15
  (g_fixture_case_mutualBroadA_x3a_0 g_fixture_case_mutualBroadB_x3a_2) = None.
Proof. reflexivity. Qed.
Example cast_parametric_identity (T : Set) (x : g_fixture_type_tagged T) :
  g_fixture_cast_16 T x = Some x.
Proof. reflexivity. Qed.
