From Coq Require Import String Ascii List ZArith.
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
