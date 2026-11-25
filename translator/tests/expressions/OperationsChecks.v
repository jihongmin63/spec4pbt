From Coq Require Import String List ZArith.
From ALCoq Require Import Execution Values.
From FixtureSpec Require Import Spec.
From FixtureSpec.Generated Require Import InductiveRelations_0000.
Import ListNotations.
Open Scope string_scope.

Ltac execute :=
  solve [repeat (first [solve [reflexivity] | solve [econstructor; reflexivity] | econstructor])].

Example subtraction_below_zero : g_fixture_dec_subtract 2 5 (-3)%Z.
Proof. unfold g_fixture_dec_subtract. eexists. constructor. Qed.
Example eager_external : exists final,
 g_fixture_dec_eager_execute {| next_fresh := 0 |} (Success false) final.
Proof.
 eexists. eapply direct_case_9.
 - apply direct_case_3 with (chosen_2 := true).
 - apply direct_case_11.
Qed.
Example byte_slice : exists final, g_fixture_dec_sliced_execute "abcd" 1 2 {| next_fresh := 0 |} (Success "bc") final.
Proof. eexists. execute. Qed.
Example list_index : exists final, g_fixture_dec_indexed_execute [2;4] 1 {| next_fresh := 0 |} (Success 4) final.
Proof. eexists. execute. Qed.
Example missing_list_index :
 g_fixture_dec_indexed_execute [2;4] 2 {| next_fresh := 0 |}
  Unmatch {| next_fresh := 0 |}.
Proof. execute. Qed.

(* Exercise public direct relations at the real host boundary, with a symbolic
   natural so the proof never allocates max_int Peano constructors. *)
Ltac solve_host_boundary H :=
  cbv beta iota zeta delta [text_splice_host_error splice_list splice_text
    slice_sum_overflows host_sum_overflows];
  rewrite ?H; reflexivity.

Example direct_text_slice_overflow n : Z.of_nat n = 4611686018427387903%Z ->
 g_fixture_dec_sliced_execute "abc" n 1 {| next_fresh := 0 |}
   (Error {| error_kind := HostInvalidArgument; error_detail := "String.sub / Bytes.sub" |})
   {| next_fresh := 0 |}.
Proof. intro H. econstructor; solve_host_boundary H. Qed.
Example direct_text_slice_count_overflow n : Z.of_nat n = 4611686018427387903%Z ->
 g_fixture_dec_sliced_execute "abc" 1 n {| next_fresh := 0 |}
   (Error {| error_kind := HostInvalidArgument; error_detail := "String.sub / Bytes.sub" |})
   {| next_fresh := 0 |}.
Proof. intro H. econstructor; solve_host_boundary H. Qed.
Example direct_text_update_overflow n : Z.of_nat n = 4611686018427387903%Z ->
 g_fixture_dec_text_x5f_slice_x5f_replace_execute "abc" n 1 "x" {| next_fresh := 0 |}
   (Error {| error_kind := HostInvalidArgument; error_detail := "String.sub / Bytes.sub" |})
   {| next_fresh := 0 |}.
Proof. intro H. econstructor; solve_host_boundary H. Qed.
Example direct_text_update_checks_length_first n : Z.of_nat n = 4611686018427387903%Z ->
 g_fixture_dec_text_x5f_slice_x5f_replace_execute "abc" n 1 "" {| next_fresh := 0 |}
   (Error {| error_kind := ALAbort; error_detail := "partial expression failed" |})
   {| next_fresh := 0 |}.
Proof. intro H. econstructor; solve_host_boundary H. Qed.
Example direct_nested_text_update_reads_parent n : Z.of_nat n = 4611686018427387903%Z ->
 g_fixture_dec_nested_x5f_text_x5f_slice_x5f_replace_execute "abc" n 1 "" {| next_fresh := 0 |}
   (Error {| error_kind := HostInvalidArgument; error_detail := "String.sub / Bytes.sub" |})
   {| next_fresh := 0 |}.
Proof. intro H. econstructor; solve_host_boundary H. Qed.
Example direct_list_update_overflow n : Z.of_nat n = 4611686018427387903%Z ->
 g_fixture_dec_slice_x5f_replace_execute [4;8] n 1 [7] {| next_fresh := 0 |}
   (Success [4;8]) {| next_fresh := 0 |}.
Proof. intro H. econstructor; solve_host_boundary H. Qed.
Example direct_list_update_checks_length n : Z.of_nat n = 4611686018427387903%Z ->
 g_fixture_dec_slice_x5f_replace_execute [4;8] n 1 [] {| next_fresh := 0 |}
   (Error {| error_kind := ALAbort; error_detail := "partial expression failed" |})
   {| next_fresh := 0 |}.
Proof. intro H. econstructor; solve_host_boundary H. Qed.
Print Assumptions direct_text_update_checks_length_first.
Print Assumptions direct_nested_text_update_reads_parent.

(* These statements quantify over every overflowing pair admitted by the host
   conversions, not just max_int + 1 or a finite sample. *)
Theorem every_text_slice_overflow s start count state :
 (Z.of_nat start <= host_int_max)%Z -> (Z.of_nat count <= host_int_max)%Z ->
 (host_int_max < Z.of_nat start + Z.of_nat count)%Z ->
 g_fixture_dec_sliced_execute s start count state
   (Error {| error_kind := HostInvalidArgument; error_detail := "String.sub / Bytes.sub" |}) state.
Proof.
 intros Hs Hc Ho. econstructor.
 - apply Z.leb_le. exact Hs.
 - apply Z.leb_le. exact Hc.
 - unfold slice_sum_overflows, host_sum_overflows. apply Z.ltb_lt. exact Ho.
Qed.
Theorem every_text_update_overflow s start count replacement state :
 (Z.of_nat start <= host_int_max)%Z -> (Z.of_nat count <= host_int_max)%Z ->
 (host_int_max < Z.of_nat start + Z.of_nat count)%Z ->
 String.length replacement = count ->
 g_fixture_dec_text_x5f_slice_x5f_replace_execute s start count replacement state
   (Error {| error_kind := HostInvalidArgument; error_detail := "String.sub / Bytes.sub" |}) state.
Proof.
 intros Hs Hc Ho Hl. econstructor.
 - apply Z.leb_le. exact Hs.
 - apply Z.leb_le. exact Hc.
 - unfold text_splice_host_error, slice_sum_overflows, host_sum_overflows.
   apply Bool.andb_true_iff. split; [apply Z.ltb_lt; exact Ho | apply Nat.eqb_eq; exact Hl].
Qed.
Theorem every_list_update_overflow xs start count replacement state :
 (Z.of_nat start <= host_int_max)%Z -> (Z.of_nat count <= host_int_max)%Z ->
 (host_int_max < Z.of_nat start + Z.of_nat count)%Z ->
 List.length replacement = count ->
 g_fixture_dec_slice_x5f_replace_execute xs start count replacement state (Success xs) state.
Proof.
 intros Hs Hc Ho Hl. econstructor.
 - apply Z.leb_le. exact Hs.
 - apply Z.leb_le. exact Hc.
 - unfold splice_list, slice_sum_overflows, host_sum_overflows.
   apply Z.ltb_lt in Ho. rewrite Ho, Hl, Nat.eqb_refl. reflexivity.
Qed.
Print Assumptions every_text_slice_overflow.
Print Assumptions every_text_update_overflow.
Print Assumptions every_list_update_overflow.
Theorem text_slice_overflow_outcome_iff s start count state outcome final :
 (Z.of_nat start <= host_int_max)%Z -> (Z.of_nat count <= host_int_max)%Z ->
 (host_int_max < Z.of_nat start + Z.of_nat count)%Z ->
 (g_fixture_dec_sliced_execute s start count state outcome final <->
  outcome = Error {| error_kind := HostInvalidArgument; error_detail := "String.sub / Bytes.sub" |} /\
  final = state).
Proof.
 intros Hs Hc Ho.
 assert (Bs : Z.leb (Z.of_nat start) 4611686018427387903 = true) by (apply Z.leb_le; exact Hs).
 assert (Bc : Z.leb (Z.of_nat count) 4611686018427387903 = true) by (apply Z.leb_le; exact Hc).
 assert (Bo : slice_sum_overflows start count = true) by
   (unfold slice_sum_overflows, host_sum_overflows; apply Z.ltb_lt; exact Ho).
 split.
 - intro H. inversion H; subst; rewrite ?Bs, ?Bc, ?Bo in *; try discriminate; split; reflexivity.
 - intros [-> ->]. apply every_text_slice_overflow; assumption.
Qed.
Print Assumptions text_slice_overflow_outcome_iff.
Example record_update : exists final, g_fixture_dec_updated_execute (g_fixture_record_box 3 7) 8 {| next_fresh := 0 |} (Success (g_fixture_record_box 8 7)) final.
Proof. eexists. execute. Qed.
Example pair_iteration : exists final, g_fixture_dec_paired_execute [1;2] [3;4] {| next_fresh := 0 |} (Success [(1,3);(2,4)]) final.
Proof. eexists. execute. Qed.
Example fixed_length_text_update : exists final, g_fixture_dec_text_x5f_replace_execute "abc" 1 "x" {| next_fresh := 0 |} (Success "axc") final.
Proof. eexists. execute. Qed.
Example rejects_text_resize :
 g_fixture_dec_text_x5f_replace_execute "a" 0 "xy" {| next_fresh := 0 |}
  (Error {| error_kind := ALAbort; error_detail := "partial expression failed" |}) {| next_fresh := 0 |}.
Proof. execute. Qed.
Example fixed_length_list_update : exists final, g_fixture_dec_slice_x5f_replace_execute [1;2;3] 1 1 [8] {| next_fresh := 0 |} (Success [1;8;3]) final.
Proof. eexists. execute. Qed.
Example rejects_list_resize :
 g_fixture_dec_slice_x5f_replace_execute [1;2] 0 2 [] {| next_fresh := 0 |}
  (Error {| error_kind := ALAbort; error_detail := "partial expression failed" |}) {| next_fresh := 0 |}.
Proof. execute. Qed.
Example nested_store_update : exists final,
 g_fixture_dec_nested_execute (g_fixture_record_store [g_fixture_record_box 1 2;g_fixture_record_box 3 4] 9) 1 8
  {| next_fresh := 0 |} (Success (g_fixture_record_store [g_fixture_record_box 1 2;g_fixture_record_box 8 4] 9)) final.
Proof. eexists. execute. Qed.
Print Assumptions subtraction_below_zero.
Print Assumptions rejects_text_resize.
Print Assumptions nested_store_update.

Example invalid_slice_is_al_error :
 g_fixture_dec_sliced_execute "a" 2 0 {| next_fresh := 0 |}
  (Error {| error_kind := ALAbort; error_detail := "partial expression failed" |}) {| next_fresh := 0 |}.
Proof. execute. Qed.

Print Assumptions eager_external.
Print Assumptions byte_slice.
Print Assumptions list_index.
Print Assumptions missing_list_index.
Print Assumptions direct_text_slice_overflow.
Print Assumptions direct_text_slice_count_overflow.
Print Assumptions direct_text_update_overflow.
Print Assumptions direct_list_update_overflow.
Print Assumptions direct_list_update_checks_length.
Print Assumptions record_update.
Print Assumptions pair_iteration.
Print Assumptions fixed_length_text_update.
Print Assumptions fixed_length_list_update.
Print Assumptions rejects_list_resize.
Print Assumptions invalid_slice_is_al_error.
