From Coq Require Import String List.
From ALCoq Require Import Execution Values.
From FixtureSpec Require Import Spec.
From FixtureSpec.Generated Require Import Bodies_0000.
Import ListNotations.
Open Scope string_scope.

Ltac execute :=
  cbn;
  first [ solve [apply eval_return]
        | solve [apply eval_unmatched]
        | solve [apply eval_raise]
        | solve [apply eval_choose]
        | solve [apply eval_fresh]
        | solve [apply eval_invoke; execute]
        | solve [eapply eval_bind_success; [execute | execute]]
        | solve [apply eval_bind_unmatch; execute]
        | solve [apply eval_bind_error; execute]
        | solve [apply eval_or_success; execute]
        | solve [eapply eval_or_unmatch; [execute | execute]]
        | solve [apply eval_or_error; execute]
        | solve [eapply eval_negate_success; execute]
        | solve [apply eval_negate_unmatch; execute]
        | solve [apply eval_negate_error; execute] ].

Example R_zero : exists final, Eval (@Body) (Invoke (C_g_fixture_rel_R 0)) {| next_fresh := 0 |} (Success 1) final.
Proof. eexists. execute. Qed.
Example R_one : exists final, Eval (@Body) (Invoke (C_g_fixture_rel_R 1)) {| next_fresh := 0 |} (Success 9) final.
Proof. eexists. execute. Qed.
Example first_clause : exists final, Eval (@Body) (Invoke (C_g_fixture_dec_first 22)) {| next_fresh := 0 |} (Success 1) final.
Proof. eexists. execute. Qed.
Example named_callback : exists final, Eval (@Body) (Invoke (C_g_fixture_dec_through 22)) {| next_fresh := 0 |} (Success 1) final.
Proof. eexists. execute. Qed.
Example error_is_propagated :
  Eval (@Body) (Invoke C_g_fixture_dec_error) {| next_fresh := 0 |}
    (Error {| error_kind := HostConversion; error_detail := "partial expression failed" |})
    {| next_fresh := 0 |}.
Proof. execute. Qed.
Example external_zero : exists final, Eval (@Body) (Invoke (C_g_fixture_rel_External 8)) {| next_fresh := 0 |} (Success 0) final.
Proof. eexists. execute. Qed.
Example external_seven : exists final, Eval (@Body) (Invoke (C_g_fixture_rel_External 8)) {| next_fresh := 0 |} (Success 7) final.
Proof. eexists. execute. Qed.
Example sink_unmatch :
  Eval (@Body) (Invoke (C_g_fixture_dec_sink nat nat_ops)) {| next_fresh := 0 |}
    Unmatch {| next_fresh := 0 |}.
Proof. execute. Qed.
Example negated_argument_unmatch :
  Eval (@Body) (Invoke (C_g_fixture_rel_NegArg 0)) {| next_fresh := 0 |}
    Unmatch {| next_fresh := 0 |}.
Proof. execute. Qed.
Example negated_argument_error :
  Eval (@Body) (Invoke (C_g_fixture_rel_NegError 0)) {| next_fresh := 0 |}
    (Error {| error_kind := HostConversion; error_detail := "partial expression failed" |})
    {| next_fresh := 0 |}.
Proof. execute. Qed.
Example eager_boolean_error :
  Eval (@Body) (Invoke C_g_fixture_dec_eager_x5f_error) {| next_fresh := 0 |}
    (Error {| error_kind := HostConversion; error_detail := "partial expression failed" |})
    {| next_fresh := 0 |}.
Proof. execute. Qed.
Example iteration_collects : exists final, Eval (@Body) (Invoke (C_g_fixture_dec_zipadd [1;2] [10;20])) {| next_fresh := 0 |} (Success [11;22]) final.
Proof. eexists. execute. Qed.
Example triple_iteration : exists final, Eval (@Body) (Invoke (C_g_fixture_dec_triple [1;2] [3;4] [5;6])) {| next_fresh := 0 |} (Success [(1,3,5);(2,4,6)]) final.
Proof. eexists. execute. Qed.
Example iteration_length_guard :
  Eval (@Body) (Invoke (C_g_fixture_dec_zipadd [1;2] [3])) {| next_fresh := 0 |}
    Unmatch {| next_fresh := 0 |}.
Proof. execute. Qed.
Example opaque_is_singleton (x : g_fixture_type_opaque) : x = g_fixture_extern_opaque.
Proof. destruct x; reflexivity. Qed.
Print Assumptions R_zero.
Print Assumptions named_callback.
Print Assumptions error_is_propagated.

Example callee_result_is_not_reselected : exists final, Eval (@Body) (Invoke (C_g_fixture_rel_M 0)) {| next_fresh := 0 |} (Success 8) final.
Proof. eexists. execute. Qed.
Example error_blocks_otherwise :
  Eval (@Body) (Invoke C_g_fixture_dec_otherwise_x5f_error) {| next_fresh := 0 |}
    (Error {| error_kind := HostConversion; error_detail := "partial expression failed" |})
    {| next_fresh := 0 |}.
Proof. execute. Qed.

Example external_relation_is_permissive : External_g_fixture_rel_External 8 7.
Proof. constructor. Qed.
Example external_relation_realizes_choice : g_fixture_rel_External 8 7.
Proof. apply External_g_fixture_rel_External_realized. constructor. Qed.

Example reused_iteration_locals_do_not_escape :
 exists final, Eval (@Body) (Invoke (C_g_fixture_dec_shadow [1;2])) {| next_fresh := 0 |}
   (Success ([2;3],[3;4])) final.
Proof. eexists. execute. Qed.
Print Assumptions reused_iteration_locals_do_not_escape.
