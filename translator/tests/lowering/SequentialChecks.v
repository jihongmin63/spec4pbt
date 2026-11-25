From Coq Require Import String List.
From ALCoq Require Import Execution Values.
From FixtureSpec Require Import Spec.
Import ListNotations.
Open Scope string_scope.

Ltac execute :=
  solve [repeat (first [solve [reflexivity] | solve [econstructor; reflexivity] | econstructor])].

Example R_zero : exists final, g_fixture_rel_R_execute 0 {| next_fresh := 0 |} (Success 1) final.
Proof. eexists. execute. Qed.
Example R_one : exists final, g_fixture_rel_R_execute 1 {| next_fresh := 0 |} (Success 9) final.
Proof. eexists. execute. Qed.
Example first_clause : exists final, g_fixture_dec_first_execute 22 {| next_fresh := 0 |} (Success 1) final.
Proof. eexists. execute. Qed.
Example named_callback : exists final, g_fixture_dec_through_execute 22 {| next_fresh := 0 |} (Success 1) final.
Proof. eexists. execute. Qed.
Example error_is_propagated :
  g_fixture_dec_error_execute {| next_fresh := 0 |}
    (Error {| error_kind := HostConversion; error_detail := "partial expression failed" |})
    {| next_fresh := 0 |}.
Proof. execute. Qed.
Example external_zero : exists final, g_fixture_rel_External_execute 8 {| next_fresh := 0 |} (Success 0) final.
Proof. eexists. execute. Qed.
Example external_seven : exists final, g_fixture_rel_External_execute 8 {| next_fresh := 0 |} (Success 7) final.
Proof. eexists. execute. Qed.
Example sink_unmatch :
  g_fixture_dec_sink_execute nat nat_ops {| next_fresh := 0 |}
    Unmatch {| next_fresh := 0 |}.
Proof. execute. Qed.
Example negated_argument_unmatch :
  g_fixture_rel_NegArg_execute 0 {| next_fresh := 0 |}
    Unmatch {| next_fresh := 0 |}.
Proof. execute. Qed.
Example negated_argument_error :
  g_fixture_rel_NegError_execute 0 {| next_fresh := 0 |}
    (Error {| error_kind := HostConversion; error_detail := "partial expression failed" |})
    {| next_fresh := 0 |}.
Proof. execute. Qed.
Example eager_boolean_error :
  g_fixture_dec_eager_x5f_error_execute {| next_fresh := 0 |}
    (Error {| error_kind := HostConversion; error_detail := "partial expression failed" |})
    {| next_fresh := 0 |}.
Proof. execute. Qed.
Example iteration_collects : exists final, g_fixture_dec_zipadd_execute [1;2] [10;20] {| next_fresh := 0 |} (Success [11;22]) final.
Proof.
  eexists. eapply direct_case_141 with (traverse_result_139 := [11;22]); try reflexivity.
  cbn [combine].
  eapply direct_case_135 with (v_2374656d703238 := 1) (v_2374656d703239 := 10)
    (traverse_rest_133 := [22]); [reflexivity |].
  eapply direct_case_135 with (v_2374656d703238 := 2) (v_2374656d703239 := 20)
    (traverse_rest_133 := []); [reflexivity | constructor].
Qed.
Example triple_iteration : exists final, g_fixture_dec_triple_execute [1;2] [3;4] [5;6] {| next_fresh := 0 |} (Success [(1,3,5);(2,4,6)]) final.
Proof.
  eexists. eapply direct_case_159 with (traverse_result_157 := [(1,3,5);(2,4,6)]); try reflexivity.
  cbn [combine].
  eapply direct_case_153; [reflexivity |].
  eapply direct_case_153; [reflexivity | constructor].
Qed.
Example iteration_length_guard :
  g_fixture_dec_zipadd_execute [1;2] [3] {| next_fresh := 0 |}
    Unmatch {| next_fresh := 0 |}.
Proof. execute. Qed.
Example opaque_is_singleton (x : g_fixture_type_opaque) : x = g_fixture_extern_opaque.
Proof. destruct x; reflexivity. Qed.
Print Assumptions R_zero.
Print Assumptions named_callback.
Print Assumptions error_is_propagated.

Example callee_result_is_not_reselected : exists final, g_fixture_rel_M_execute 0 {| next_fresh := 0 |} (Success 8) final.
Proof. eexists. execute. Qed.
Example error_blocks_otherwise :
  g_fixture_dec_otherwise_x5f_error_execute {| next_fresh := 0 |}
    (Error {| error_kind := HostConversion; error_detail := "partial expression failed" |})
    {| next_fresh := 0 |}.
Proof. execute. Qed.

Example external_relation_is_permissive : External_g_fixture_rel_External 8 7.
Proof. constructor. Qed.
Example external_relation_realizes_choice : g_fixture_rel_External 8 7.
Proof. apply External_g_fixture_rel_External_realized. constructor. Qed.

Example reused_iteration_locals_do_not_escape :
 exists final, g_fixture_dec_shadow_execute [1;2] {| next_fresh := 0 |}
   (Success ([2;3],[3;4])) final.
Proof.
  eexists. eapply direct_case_233 with (traverse_result_220 := [2;3])
    (traverse_result_231 := [3;4]).
  - eapply direct_case_216 with (v_2374656d703732 := 1)
      (traverse_rest_214 := [3]); [reflexivity |].
    eapply direct_case_216 with (v_2374656d703732 := 2)
      (traverse_rest_214 := []); [reflexivity | constructor].
  - eapply direct_case_227 with (v_2374656d703736 := 1)
      (traverse_rest_225 := [4]); [reflexivity |].
    eapply direct_case_227 with (v_2374656d703736 := 2)
      (traverse_rest_225 := []); [reflexivity | constructor].
Qed.
Print Assumptions reused_iteration_locals_do_not_escape.

Print Assumptions R_one.
Print Assumptions first_clause.
Print Assumptions external_zero.
Print Assumptions external_seven.
Print Assumptions sink_unmatch.
Print Assumptions negated_argument_unmatch.
Print Assumptions negated_argument_error.
Print Assumptions eager_boolean_error.
Print Assumptions iteration_collects.
Print Assumptions triple_iteration.
Print Assumptions iteration_length_guard.
Print Assumptions opaque_is_singleton.
Print Assumptions callee_result_is_not_reselected.
Print Assumptions error_blocks_otherwise.
Print Assumptions external_relation_is_permissive.
Print Assumptions external_relation_realizes_choice.
