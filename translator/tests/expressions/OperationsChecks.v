From Coq Require Import String List ZArith.
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

Example subtraction_below_zero : g_fixture_dec_subtract 2 5 (-3)%Z.
Proof. unfold g_fixture_dec_subtract. eexists. constructor. Qed.
Example eager_external : exists final,
 Eval (@Body) (Invoke C_g_fixture_dec_eager) {| next_fresh := 0 |} (Success false) final.
Proof.
 eexists. apply eval_invoke. cbn. apply eval_or_success.
 eapply eval_bind_success; [apply eval_return |].
 eapply eval_bind_success with (value := true); [apply eval_invoke; apply eval_choose | apply eval_return].
Qed.
Example byte_slice : exists final, Eval (@Body) (Invoke (C_g_fixture_dec_sliced "abcd" 1 2)) {| next_fresh := 0 |} (Success "bc") final.
Proof. eexists. execute. Qed.
Example list_index : exists final, Eval (@Body) (Invoke (C_g_fixture_dec_indexed [2;4] 1)) {| next_fresh := 0 |} (Success 4) final.
Proof. eexists. execute. Qed.
Example missing_list_index :
 Eval (@Body) (Invoke (C_g_fixture_dec_indexed [2;4] 2)) {| next_fresh := 0 |}
  Unmatch {| next_fresh := 0 |}.
Proof. execute. Qed.
Example record_update : exists final, Eval (@Body) (Invoke (C_g_fixture_dec_updated (g_fixture_record_box 3 7) 8)) {| next_fresh := 0 |} (Success (g_fixture_record_box 8 7)) final.
Proof. eexists. execute. Qed.
Example pair_iteration : exists final, Eval (@Body) (Invoke (C_g_fixture_dec_paired [1;2] [3;4])) {| next_fresh := 0 |} (Success [(1,3);(2,4)]) final.
Proof. eexists. execute. Qed.
Example fixed_length_text_update : exists final, Eval (@Body) (Invoke (C_g_fixture_dec_text_x5f_replace "abc" 1 "x")) {| next_fresh := 0 |} (Success "axc") final.
Proof. eexists. execute. Qed.
Example rejects_text_resize :
 Eval (@Body) (Invoke (C_g_fixture_dec_text_x5f_replace "a" 0 "xy")) {| next_fresh := 0 |}
  (Error {| error_kind := ALAbort; error_detail := "partial expression failed" |}) {| next_fresh := 0 |}.
Proof. execute. Qed.
Example fixed_length_list_update : exists final, Eval (@Body) (Invoke (C_g_fixture_dec_slice_x5f_replace [1;2;3] 1 1 [8])) {| next_fresh := 0 |} (Success [1;8;3]) final.
Proof. eexists. execute. Qed.
Example rejects_list_resize :
 Eval (@Body) (Invoke (C_g_fixture_dec_slice_x5f_replace [1;2] 0 2 [])) {| next_fresh := 0 |}
  (Error {| error_kind := ALAbort; error_detail := "partial expression failed" |}) {| next_fresh := 0 |}.
Proof. execute. Qed.
Example nested_store_update : exists final,
 Eval (@Body) (Invoke (C_g_fixture_dec_nested (g_fixture_record_store [g_fixture_record_box 1 2;g_fixture_record_box 3 4] 9) 1 8))
  {| next_fresh := 0 |} (Success (g_fixture_record_store [g_fixture_record_box 1 2;g_fixture_record_box 8 4] 9)) final.
Proof. eexists. execute. Qed.
Print Assumptions subtraction_below_zero.
Print Assumptions rejects_text_resize.
Print Assumptions nested_store_update.

Example invalid_slice_is_al_error :
 Eval (@Body) (Invoke (C_g_fixture_dec_sliced "a" 2 0)) {| next_fresh := 0 |}
  (Error {| error_kind := ALAbort; error_detail := "partial expression failed" |}) {| next_fresh := 0 |}.
Proof. execute. Qed.
