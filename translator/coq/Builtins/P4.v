From Coq Require Import List String Bool ZArith.
From ALCoq Require Import Execution Values.
From ALCoq.Builtins Require Import Common.
Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.
Open Scope string_scope.
Local Open Scope Z_scope.

Definition sum_nat {Call} (xs : list nat) : Action Call nat := Return (fold_left Nat.add xs 0%nat).
Definition max_nat {Call} (xs : list nat) : Action Call nat :=
  match xs with [] => Unmatched | x :: rest => Return (fold_left Nat.max rest x) end.
Definition min_nat {Call} (xs : list nat) : Action Call nat :=
  match xs with [] => Unmatched | x :: rest => Return (fold_left Nat.min rest x) end.
Definition sum_int {Call} (xs : list Z) : Action Call Z := Return (fold_left Z.add xs 0).
Definition max_int {Call} (xs : list Z) : Action Call Z :=
  Return (match xs with [] => 0 | x :: rest => fold_left Z.max rest x end).
Definition min_int {Call} (xs : list Z) : Action Call Z :=
  Return (match xs with [] => 0 | x :: rest => fold_left Z.min rest x end).
Definition text_to_int {Call} (s : string) : Action Call Z :=
  match parse_integer s with Some z => Return z | None => host_error "Bigint.of_string" end.
Definition int_to_text {Call} (z : Z) : Action Call string := Return (print_int z).
Definition split_text {Call} (text separator : string) : Action Call (list string) :=
  match separator with
  | String c EmptyString => Return (split_byte c text)
  | _ => host_error "split_text: separator length must be one" end.
Definition strip_prefix {Call} (text prefix : string) : Action Call string :=
  if starts_with prefix text then Return (drop_text (String.length prefix) text)
  else host_error "strip_prefix: prefix assertion".
Definition strip_suffix {Call} (text suffix : string) : Action Call string :=
  let n := (String.length text - String.length suffix)%nat in
  if andb (Nat.leb (String.length suffix) (String.length text)) (String.eqb (drop_text n text) suffix)
  then Return (take_text n text) else host_error "strip_suffix: suffix assertion".
Definition strip_all_whitespace {Call} (text : string) : Action Call string := Return (remove_spaces text).
Definition rev_ {Call A} (xs : list A) : Action Call (list A) := Return (rev xs).
Definition concat_ {Call A} (xs : list (list A)) : Action Call (list A) := Return (List.concat xs).
Definition distinct_ {Call A} (ops : ValueOps A) (xs : list A) : Action Call bool :=
  Return (Nat.eqb (List.length (canonical_set ops xs)) (List.length xs)).
Definition partition_ {Call A} (xs : list A) (n : nat) : Action Call (list A * list A) :=
  if Z.leb (Z.of_nat n) host_max then Return (firstn n xs, skipn n xs)
  else host_error "partition_: Bigint.to_int_exn".
Definition assoc_ {Call K V} (ops : ValueOps K) (key : K) (xs : list (K * V)) : Action Call (option V) :=
  Return (assoc_first (comparison_eq ops) key xs).
Definition sort_ {Call A} (xs : list (nat * A)) : Action Call (list (nat * A)) :=
  Return (stable_sort (fun x y => Nat.compare (fst x) (fst y)) xs).
Definition transpose_ {Call A} (rows : list (list A)) : Action Call (list (list A)) :=
  match rows with
  | [] => Return []
  | row :: _ => if forallb (fun r => Nat.eqb (List.length row) (List.length r)) rows
                then Return (transpose_width (List.length row) rows) else Unmatched end.
Definition intersect_set {Call A} (ops : ValueOps A) (xs ys : list A) : Action Call (list A) :=
  Return (filter (fun x => member (comparison_eq ops) x ys) (canonical_set ops xs)).
Definition union_set {Call A} (ops : ValueOps A) (xs ys : list A) : Action Call (list A) :=
  Return (canonical_set ops (List.app xs ys)).
Definition unions_set {Call A} (ops : ValueOps A) (xs : list (list A)) : Action Call (list A) :=
  Return (canonical_set ops (List.concat xs)).
Definition diff_set {Call A} (ops : ValueOps A) (xs ys : list A) : Action Call (list A) :=
  Return (filter (fun x => negb (member (comparison_eq ops) x ys)) (canonical_set ops xs)).
Definition sub_set {Call A} (ops : ValueOps A) (xs ys : list A) : Action Call bool :=
  Return (forallb (fun x => member (comparison_eq ops) x ys) xs).
Definition eq_set {Call A} (ops : ValueOps A) (xs ys : list A) : Action Call bool :=
  Return (equal_list (comparison_eq ops) (canonical_set ops xs) (canonical_set ops ys)).
Definition find_map {Call K V} (ops : ValueOps K) (xs : list (K * V)) (key : K) : Action Call (option V) :=
  Return (assoc_first (equal_value ops) key xs).
Definition find_maps {Call K V} (ops : ValueOps K) (xs : list (list (K * V))) (key : K) : Action Call (option V) :=
  Return (find_many (equal_value ops) xs key).
Definition add_map {Call K V} (ops : ValueOps K) (xs : list (K * V)) (key : K) (value : V) : Action Call (list (K * V)) :=
  Return (update_first (equal_value ops) key value xs).
Definition adds_map {Call K V} (ops : ValueOps K) (xs : list (K * V)) (keys : list K) (values : list V) : Action Call (list (K * V)) :=
  match update_many (equal_value ops) xs keys values with
  | Some result => Return result | None => host_error "List.fold_left2: length mismatch" end.
Definition update_map := @add_map.
Arguments update_map {Call K V} _ _ _ _.
Definition fresh_typeId {Call} : Action Call string :=
  Bind Fresh (fun n => Return (String.append "FRESH__" (print_nat n))).

(* Source shl'/shr' treat nonpositive offsets as zero; shr' uses truncating
   division, whereas bitacc uses arithmetic right shift. *)
Definition power (width : Z) : Z := Z.pow 2 (Z.max 0 width).
Fixpoint shrink (count : nat) (value modulus : Z) : Z :=
  match count with O => value | S n => shrink n (Z.quot value 2 + modulus) modulus end.
Definition shl {Call} (value offset : Z) : Action Call Z :=
  if Z.gtb offset 2048 then Unmatched else Return (value * power offset).
Definition shr {Call} (value offset : Z) : Action Call Z :=
  if Z.gtb offset 2048 then Unmatched else Return (Z.quot value (power offset)).
Definition shr_arith {Call} (value offset modulus : Z) : Action Call Z :=
  if Z.gtb offset 2048 then Unmatched else Return (shrink (Z.to_nat offset) value modulus).
Definition pow2 {Call} (width : Z) : Action Call Z := Return (power width).
Definition bitstr_to_int {Call} (width value : Z) : Action Call Z :=
  if Z.gtb width 2048 then Unmatched else
  if Z.leb width 0 then Return 0 else
  let modulus := power width in
  let half := Z.quot modulus 2 in
  Return ((value + half) mod modulus - half).
Definition int_to_bitstr {Call} (width value : Z) : Action Call Z :=
  if Z.gtb width 2048 then Unmatched else Return (value mod power width).
Definition bits_unsigned (bits : list bool) : Z :=
  fold_left (fun (acc : Z) (bit : bool) => 2 * acc + if bit then 1 else 0) bits 0.
Definition bits_to_int_unsigned {Call} (bits : list bool) : Action Call Z := Return (bits_unsigned bits).
Definition bits_to_int_signed {Call} (bits : list bool) : Action Call Z :=
  match bits with
  | [] => Unmatched
  | sign :: _ => Return (bits_unsigned bits - if sign then power (Z.of_nat (List.length bits)) else 0) end.
Definition int_to_bits_unsigned {Call} (width value : Z) : Action Call (list bool) :=
  if Z.gtb width 2048 then Unmatched else
  if Z.ltb width 0 then host_error "Array.init: negative width" else
  Return (map (fun n => Z.testbit value (Z.of_nat n)) (rev (seq 0 (Z.to_nat width)))).
Definition int_to_bits_signed := @int_to_bits_unsigned.
Arguments int_to_bits_signed {Call} _ _.
Definition bneg {Call} (value : Z) : Action Call Z := Return (Z.lnot value).
Definition band {Call} (x y : Z) : Action Call Z := Return (Z.land x y).
Definition bxor {Call} (x y : Z) : Action Call Z := Return (Z.lxor x y).
Definition bor {Call} (x y : Z) : Action Call Z := Return (Z.lor x y).
Definition bitacc {Call} (value high low : Z) : Action Call Z :=
  if Z.ltb low 0 then host_error "bitslice x[y:z] must have y > z > 0" else
  if negb (fits_host low) then host_error "Bigint.to_int_exn" else
  Return (Z.land (Z.shiftr value low) (power (high + 1 - low) - 1)).
Definition bitacc_replace {Call} (value high low rhs : Z) : Action Call Z :=
  if negb (fits_host low) then host_error "Bigint.to_int_exn" else
  if Z.ltb low 0 then host_error "Bigint.shift_left: negative shift" else
  let mask_hi := power (high + 1) - 1 in
  let mask_lo := power low - 1 in
  Return (Z.lxor (Z.land value (Z.lnot (Z.lxor mask_hi mask_lo))) (Z.shiftl rhs low)).
Definition print_ {Call A} (ops : ValueOps A) (value : A) : Action Call string :=
  match unparse_value ops value with
  | Some text => Return text | None => host_error "P4.Unparse: unsupported value" end.
