From Coq Require Import String Ascii List ZArith Lia.
From ALCoq Require Import Execution Values.
Import ListNotations.
Open Scope Z_scope.

(* Truncated subtraction, Euclidean rather than truncating division, unchecked
   indexing, or comparing function bodies would break these boundary cases. *)
Example negative_nat_subtraction : subtract_nat 2 5 = -3.
Proof. reflexivity. Qed.
Example integer_truncation : divide_int (-7) 3 = Some (-2).
Proof. reflexivity. Qed.
Example remainder_sign : remainder_int (-7) 3 = Some (-1).
Proof. reflexivity. Qed.
Example zero_division : divide_int 1 0 = None.
Proof. reflexivity. Qed.
Example ordered_bytes : compare_text "ab" "ac" = Lt.
Proof. reflexivity. Qed.
Example missing_index : @index_list nat [4%nat; 8%nat] 2 = None.
Proof. reflexivity. Qed.
Example empty_tail_slice : @slice_list nat [4%nat;8%nat] 2 0 = Some [].
Proof. reflexivity. Qed.
Example overflowing_slice : @slice_list nat [4%nat;8%nat] 1 2 = None.
Proof. reflexivity. Qed.
Example host_sum_wraps_list_slice : @slice_list_at_limit nat 3 [] 3 1 = Some [].
Proof. reflexivity. Qed.
Example host_sum_does_not_wrap_at_limit : @slice_list_at_limit nat 3 [4%nat;8%nat;9%nat] 1 2 = Some [8%nat;9%nat].
Proof. reflexivity. Qed.
Example splice_once : @splice_list nat [1%nat;2%nat;3%nat] 1 1 [8%nat] =
                     Some [1%nat;8%nat;3%nat].
Proof. reflexivity. Qed.
Example integer_print_sign : print_int 7 = "+7"%string.
Proof. reflexivity. Qed.
Example nat_print_no_sign : print_nat 7 = "7"%string.
Proof. reflexivity. Qed.
Example escaped_text : print_text (String (ascii_of_nat 10) "x") =
  String (ascii_of_nat 92) (String "n"%char (String "x"%char "")) .
Proof. reflexivity. Qed.
Example native_positive_integer : unparse_value int_ops 7 = Some "7"%string.
Proof. reflexivity. Qed.
Example native_list_layout : unparse_value (list_ops nat_ops) [1%nat;2%nat] = Some "1 2"%string.
Proof. reflexivity. Qed.
Example polymorphic_list_equal :
  equal_value (list_ops nat_ops) [1%nat;2%nat] [1%nat;3%nat] = false.
Proof. reflexivity. Qed.

Example splice_rejects_wrong_length : @splice_list nat [1%nat;2%nat] 0 1 [8%nat;9%nat] = None.
Proof. reflexivity. Qed.
Example text_index_replacement_is_one_byte : splice_text "a" 0 1 "xy" = None.
Proof. reflexivity. Qed.

(* Native OCaml wraps max_int + 1 below zero; List.mapi changes no elements. *)
Example native_list_update_sum_overflow (start : nat) :
  Z.of_nat start = 4611686018427387903 ->
  @splice_list nat [] start 1 [7%nat] = Some [].
Proof.
  intro H. unfold splice_list, slice_sum_overflows, host_sum_overflows.
  rewrite H. reflexivity.
Qed.

Example native_list_update_wrong_length (start : nat) :
  Z.of_nat start = 4611686018427387903 ->
  @splice_list nat [4%nat;8%nat] start 1 [] = None.
Proof. intro H. unfold splice_list, slice_sum_overflows, host_sum_overflows.
  rewrite H. reflexivity. Qed.
Example native_list_update_keeps_elements (start : nat) :
  Z.of_nat start = 4611686018427387903 ->
  @splice_list nat [4%nat;8%nat] start 1 [7%nat] = Some [4%nat;8%nat].
Proof. intro H. unfold splice_list, slice_sum_overflows, host_sum_overflows.
  rewrite H. reflexivity. Qed.
Example native_text_update_host_exception (start : nat) :
  Z.of_nat start = 4611686018427387903 -> text_splice_host_error start 1 "x" = true.
Proof. intro H. unfold text_splice_host_error, slice_sum_overflows, host_sum_overflows.
  rewrite H. reflexivity. Qed.
Example native_text_update_length_before_exception (start : nat) :
  Z.of_nat start = 4611686018427387903 -> text_splice_host_error start 1 "" = false.
Proof. intro H. unfold text_splice_host_error, slice_sum_overflows, host_sum_overflows.
  rewrite H. reflexivity. Qed.

(* Arithmetic correspondence to OCaml's signed 63-bit addition, for every pair
   accepted by Bigint.to_int_exn, including sums above max_int. *)
Definition native_signed_sum (a b : Z) :=
  ((a + b + 4611686018427387904) mod 9223372036854775808 - 4611686018427387904)%Z.
Lemma host_overflow_matches_native (a b : Z) :
  0 <= a <= host_int_max -> 0 <= b <= host_int_max ->
  host_sum_overflows a b = (native_signed_sum a b <? 0).
Proof.
  unfold host_sum_overflows, native_signed_sum, host_int_max.
  intros Ha Hb. destruct (4611686018427387903 <? a + b) eqn:Hsum.
  - apply Z.ltb_lt in Hsum. symmetry. apply Z.ltb_lt.
    replace (a+b+4611686018427387904) with
      ((a+b-4611686018427387904) + 1*9223372036854775808) by lia.
    rewrite Z.mod_add by lia. rewrite Z.mod_small; lia.
  - apply Z.ltb_ge in Hsum. rewrite Z.mod_small by lia.
    symmetry. apply Z.ltb_ge. lia.
Qed.
Print Assumptions host_overflow_matches_native.
