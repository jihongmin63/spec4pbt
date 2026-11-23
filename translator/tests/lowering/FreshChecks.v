From Coq Require Import String List ZArith.
From ALCoq Require Import Execution Values.
From P4Spec Require Import Spec.
From P4Spec.Generated Require Import Bodies_0000.
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

Example failed_path_consumes_fresh :
 Eval (@Body) (Invoke (C_g_p4_rel_Paths 0)) {| next_fresh := 0 |}
  (Success "FRESH__1") {| next_fresh := 2 |}.
Proof. execute. Qed.
Example paths_second_result : exists final,
 Eval (@Body) (Invoke (C_g_p4_rel_Paths 0)) {| next_fresh := 0 |}
  (Success "FRESH__1") final.
Proof. eexists. execute. Qed.
Example independent_iteration_locals :
 Eval (@Body) (Invoke (C_g_p4_dec_twice [1;2] [3;4])) {| next_fresh := 0 |}
  (Success (["FRESH__0";"FRESH__1"],["FRESH__2";"FRESH__3"])) {| next_fresh := 4 |}.
Proof. execute. Qed.
Print Assumptions failed_path_consumes_fresh.
Print Assumptions independent_iteration_locals.

Example boolean_effects_are_ordered :
 Eval (@Body) (Invoke C_g_p4_dec_both) {| next_fresh := 0 |}
  (Success true) {| next_fresh := 2 |}.
Proof. execute. Qed.
Example false_left_still_runs_right :
 Eval (@Body) (Invoke C_g_p4_dec_both_x5f_false) {| next_fresh := 0 |}
  (Success false) {| next_fresh := 2 |}.
Proof. execute. Qed.
Print Assumptions boolean_effects_are_ordered.
Print Assumptions false_left_still_runs_right.

Example common_match_is_reexecuted_after_unmatch :
 Eval (@Body) (Invoke (C_g_p4_rel_Common "FRESH__0")) {| next_fresh := 0 |}
  Unmatch {| next_fresh := 2 |}.
Proof. execute. Qed.
Example second_common_match_consumes_next_fresh :
 Eval (@Body) (Invoke (C_g_p4_rel_Common "FRESH__1")) {| next_fresh := 0 |}
  (Success 7) {| next_fresh := 2 |}.
Proof. execute. Qed.
Print Assumptions common_match_is_reexecuted_after_unmatch.
