From Coq Require Import ZArith String List Ascii.
From ALCoq Require Import Execution Values.
From ALCoq.Builtins Require Import Common P4.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Set Universe Polymorphism.
Unset Automatic Proposition Inductives.
Inductive NoCall : Type -> Type := .
Definition run {A} (a : Action NoCall A) := a.
Example nat_sum : run (P4.sum_nat [1;2;3]%nat) = Return 6%nat. Proof. vm_compute. reflexivity. Qed.
Example nat_max : run (P4.max_nat [1;3;2]%nat) = Return 3%nat. Proof. vm_compute. reflexivity. Qed.
Example nat_min : run (P4.min_nat [2;1;3]%nat) = Return 1%nat. Proof. vm_compute. reflexivity. Qed.
Example empty_nat_extrema : run (P4.max_nat []) = Unmatched /\ run (P4.min_nat []) = Unmatched. Proof. split; reflexivity. Qed.
Example int_sum : run (P4.sum_int [-3;2]) = Return (-1). Proof. reflexivity. Qed.
Example int_extrema : run (P4.max_int []) = Return 0 /\ run (P4.min_int []) = Return 0 /\ run (P4.max_int [-3;-1]) = Return (-1) /\ run (P4.min_int [-3;-1]) = Return (-3). Proof. repeat split; reflexivity. Qed.
Example integer_text : run (P4.int_to_text 0) = Return "+0" /\ run (P4.int_to_text (-7)) = Return "-7". Proof. split; reflexivity. Qed.
Example parse_integer : run (P4.text_to_int "-0xff") = Return (-255) /\ run (P4.text_to_int "1_024") = Return 1024. Proof. vm_compute. split; reflexivity. Qed.
Example parse_empty_and_prefix : run (P4.text_to_int "") = Return 0 /\ run (P4.text_to_int "+") = Return 0 /\ run (P4.text_to_int "0x") = Return 0. Proof. repeat split; reflexivity. Qed.
Example parse_leading_underscore : run (P4.text_to_int "_1") = host_error "Bigint.of_string" /\ run (P4.text_to_int "0x_f") = host_error "Bigint.of_string". Proof. split; reflexivity. Qed.
Example split_preserves_empty : run (P4.split_text ",a,," ",") = Return ["";"a";"";""]. Proof. reflexivity. Qed.
Example strip_text : run (P4.strip_prefix "abc" "ab") = Return "c" /\ run (P4.strip_suffix "abc" "bc") = Return "a". Proof. split; reflexivity. Qed.
Example whitespace_is_space_only : run (P4.strip_all_whitespace (" a" ++ String (ascii_of_nat 9) " b")) = Return ("a" ++ String (ascii_of_nat 9) "b"). Proof. reflexivity. Qed.
Example reverse_concat : run (P4.rev_ [1;2]) = Return [2;1] /\ run (P4.concat_ [[1];[];[2;3]]) = Return [1;2;3]. Proof. split; reflexivity. Qed.
Example distinct_structural : run (P4.distinct_ nat_ops [1;2;1]%nat) = Return false. Proof. reflexivity. Qed.
Example partition_long : run (P4.partition_ [1;2] 5%nat) = Return ([1;2],[]). Proof. reflexivity. Qed.
Example association_first : run (P4.assoc_ nat_ops 1%nat [(1%nat,"a");(1%nat,"b")]) = Return (Some "a"). Proof. reflexivity. Qed.
Example stable_sort : run (P4.sort_ [(2%nat,"b");(1%nat,"a");(2%nat,"c")]) = Return [(1%nat,"a");(2%nat,"b");(2%nat,"c")]. Proof. reflexivity. Qed.
Example transpose_rectangular : run (P4.transpose_ [[1;2];[3;4]]) = Return [[1;3];[2;4]]. Proof. reflexivity. Qed.
Example transpose_ragged : run (P4.transpose_ [[1];[2;3]]) = Unmatched. Proof. reflexivity. Qed.
Example set_sort_dedup : run (P4.union_set nat_ops [3;1;1]%nat [2;1]%nat) = Return [1;2;3]%nat. Proof. reflexivity. Qed.
Example set_intersection : run (P4.intersect_set nat_ops [3;1;1]%nat [2;1]%nat) = Return [1]%nat. Proof. reflexivity. Qed.
Example set_union_many : run (P4.unions_set nat_ops [[3;1];[2;1]]%nat) = Return [1;2;3]%nat. Proof. reflexivity. Qed.
Example set_difference : run (P4.diff_set nat_ops [3;1;1]%nat [2;1]%nat) = Return [3]%nat. Proof. reflexivity. Qed.
Example set_predicates : run (P4.sub_set nat_ops [1;1]%nat [1;2]%nat) = Return true /\ run (P4.eq_set nat_ops [2;1;1]%nat [1;2]%nat) = Return true. Proof. split; reflexivity. Qed.
Example map_first : run (P4.find_map nat_ops [(1%nat,"a");(1%nat,"b")] 1%nat) = Return (Some "a"). Proof. reflexivity. Qed.
Example maps_first : run (P4.find_maps nat_ops [[(1%nat,"a")];[(1%nat,"b")]] 1%nat) = Return (Some "a"). Proof. reflexivity. Qed.
Example map_update_first : run (P4.add_map nat_ops [(1%nat,"a");(1%nat,"b")] 1%nat "c") = Return [(1%nat,"c");(1%nat,"b")]. Proof. reflexivity. Qed.
Example map_update_missing_appends : run (P4.update_map nat_ops [(1%nat,"a")] 2%nat "b") = Return [(1%nat,"a");(2%nat,"b")]. Proof. reflexivity. Qed.
Example map_add_many : run (P4.adds_map nat_ops [(1%nat,"a")] [2;1]%nat ["b";"c"]) = Return [(1%nat,"c");(2%nat,"b")]. Proof. reflexivity. Qed.
Example shifts_negative_offsets : run (P4.shl 7 (-1)) = Return 7 /\ run (P4.shr (-7) 1) = Return (-3) /\ run (P4.shr_arith 7 2 8) = Return 13. Proof. repeat split; reflexivity. Qed.
Example shift_limit : run (P4.shl 1 2049) = Unmatched. Proof. reflexivity. Qed.
Example power_negative : run (P4.pow2 (-3)) = Return 1. Proof. reflexivity. Qed.
Example bitstring_conversions : run (P4.bitstr_to_int 4 15) = Return (-1) /\ run (P4.bitstr_to_int 0 99) = Return 0 /\ run (P4.int_to_bitstr 4 (-1)) = Return 15 /\ run (P4.int_to_bitstr (-1) 99) = Return 0. Proof. repeat split; reflexivity. Qed.
Example bits_conversions : run (P4.bits_to_int_unsigned [true;false;true]) = Return 5 /\ run (P4.bits_to_int_signed [true;false;true]) = Return (-3) /\ run (P4.bits_to_int_signed []) = Unmatched /\ run (P4.int_to_bits_unsigned 3 (-3)) = Return [true;false;true] /\ run (P4.int_to_bits_signed 3 (-3)) = Return [true;false;true]. Proof. repeat split; reflexivity. Qed.
Example bitwise : run (P4.bneg 5) = Return (-6) /\ run (P4.band 5 3) = Return 1 /\ run (P4.bxor 5 3) = Return 6 /\ run (P4.bor 5 3) = Return 7. Proof. repeat split; reflexivity. Qed.
Example bit_access : run (P4.bitacc 171 5 2) = Return 10 /\ run (P4.bitacc_replace 171 5 2 1) = Return 135. Proof. split; reflexivity. Qed.
Example print_actual_value : run (P4.print_ int_ops 7) = Return "7". Proof. reflexivity. Qed.
Example host_parse_failure : run (P4.text_to_int "not-a-number") = host_error "Bigint.of_string". Proof. reflexivity. Qed.
Example host_split_failure : run (P4.split_text "abc" "") = host_error "split_text: separator length must be one". Proof. reflexivity. Qed.
Example host_strip_failures :
  run (P4.strip_prefix "abc" "x") = host_error "strip_prefix: prefix assertion" /\
  run (P4.strip_suffix "abc" "x") = host_error "strip_suffix: suffix assertion".
Proof. split; reflexivity. Qed.
Example host_map_failure : run (P4.adds_map nat_ops [] [1]%nat ([] : list string)) = host_error "List.fold_left2: length mismatch". Proof. reflexivity. Qed.
Example host_bits_failure : run (P4.int_to_bits_unsigned (-1) 1) = host_error "Array.init: negative width". Proof. reflexivity. Qed.
Example host_bitacc_failure : run (P4.bitacc 1 2 (-1)) = host_error "bitslice x[y:z] must have y > z > 0". Proof. reflexivity. Qed.
Example host_replace_failure : run (P4.bitacc_replace 1 2 (-1) 0) = host_error "Bigint.shift_left: negative shift". Proof. reflexivity. Qed.
Example width_failures : run (P4.bitstr_to_int 2049 0) = Unmatched /\ run (P4.int_to_bitstr 2049 0) = Unmatched /\ run (P4.int_to_bits_unsigned 2049 0) = Unmatched /\ run (P4.int_to_bits_signed 2049 0) = Unmatched. Proof. repeat split; reflexivity. Qed.
Example shift_limit_inclusive : run (P4.shl 0 2048) = Return 0 /\ run (P4.shr 0 2048) = Return 0. Proof. vm_compute; split; reflexivity. Qed.
Definition differing_ops : ValueOps nat :=
  {| equal_value := fun _ _ => false; compare_value := Nat.compare;
     print_value := print_value nat_ops; unparse_value := unparse_value nat_ops |}.
Example equality_order_separation :
  run (P4.distinct_ differing_ops [1;1]%nat) = Return false /\
  run (P4.assoc_ differing_ops 1%nat [(1%nat,"a")]) = Return (Some "a") /\
  run (P4.find_map differing_ops [(1%nat,"a")] 1%nat) = Return None.
Proof. repeat split; reflexivity. Qed.
