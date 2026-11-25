From Coq Require Import String List ZArith.
From ALCoq Require Import Execution Values.
From P4Spec Require Import Spec.
Import ListNotations.
Open Scope string_scope.

Ltac execute :=
  solve [repeat (first [solve [reflexivity] | solve [econstructor; reflexivity] | econstructor])].

Example failed_path_consumes_fresh :
 g_p4_rel_Paths_execute 0 {| next_fresh := 0 |}
  (Success "FRESH__1") {| next_fresh := 2 |}.
Proof. execute. Qed.
Example paths_second_result : exists final,
 g_p4_rel_Paths_execute 0 {| next_fresh := 0 |}
  (Success "FRESH__1") final.
Proof. eexists. execute. Qed.
Example independent_iteration_locals :
 g_p4_dec_twice_execute [1;2] [3;4] {| next_fresh := 0 |}
  (Success (["FRESH__0";"FRESH__1"],["FRESH__2";"FRESH__3"])) {| next_fresh := 4 |}.
Proof.
  eapply direct_case_82 with
    (traverse_result_60 := ["FRESH__0";"FRESH__1"])
    (traverse_result_80 := ["FRESH__2";"FRESH__3"]);
    execute.
Qed.
Print Assumptions failed_path_consumes_fresh.
Print Assumptions independent_iteration_locals.

Example boolean_effects_are_ordered :
 g_p4_dec_both_execute {| next_fresh := 0 |}
  (Success true) {| next_fresh := 2 |}.
Proof. execute. Qed.
Example false_left_still_runs_right :
 g_p4_dec_both_x5f_false_execute {| next_fresh := 0 |}
  (Success false) {| next_fresh := 2 |}.
Proof. execute. Qed.
Print Assumptions boolean_effects_are_ordered.
Print Assumptions false_left_still_runs_right.

Example common_match_is_reexecuted_after_unmatch :
 g_p4_rel_Common_execute "FRESH__0" {| next_fresh := 0 |}
  Unmatch {| next_fresh := 2 |}.
Proof. execute. Qed.
Example second_common_match_consumes_next_fresh :
 g_p4_rel_Common_execute "FRESH__1" {| next_fresh := 0 |}
  (Success 7) {| next_fresh := 2 |}.
Proof. execute. Qed.
Print Assumptions common_match_is_reexecuted_after_unmatch.

Print Assumptions paths_second_result.
Print Assumptions second_common_match_consumes_next_fresh.
