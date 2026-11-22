From Coq Require Import List String Ascii Bool ZArith.
From ALCoq Require Import Execution Values.
Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.
Open Scope string_scope.

(* Pure helpers shared by profile implementations.  Structural comparison is
   deliberately separate from the language's equality operation. *)
Definition comparison_eq {A} (ops : ValueOps A) (x y : A) : bool :=
  match compare_value ops x y with Eq => true | _ => false end.
Fixpoint insert_unique {A} (cmp : A -> A -> comparison) (x : A) (xs : list A) : list A :=
  match xs with
  | [] => [x]
  | y :: ys => match cmp x y with
               | Lt => x :: xs | Eq => xs | Gt => y :: insert_unique cmp x ys end
  end.
Fixpoint canonical_set {A} (ops : ValueOps A) (xs : list A) : list A :=
  match xs with [] => [] | x :: rest => insert_unique (compare_value ops) x (canonical_set ops rest) end.
Definition member {A} (eqb : A -> A -> bool) (x : A) (xs : list A) : bool :=
  existsb (eqb x) xs.
Fixpoint stable_insert {A} (cmp : A -> A -> comparison) (x : A) (xs : list A) : list A :=
  match xs with
  | [] => [x]
  | y :: rest => match cmp x y with
                 | Gt => y :: stable_insert cmp x rest | _ => x :: xs end
  end.
Fixpoint stable_sort {A} (cmp : A -> A -> comparison) (xs : list A) : list A :=
  match xs with [] => [] | x :: rest => stable_insert cmp x (stable_sort cmp rest) end.
Fixpoint assoc_first {K V} (eqb : K -> K -> bool) (key : K) (xs : list (K * V)) : option V :=
  match xs with [] => None | (k,v) :: rest => if eqb key k then Some v else assoc_first eqb key rest end.
Fixpoint update_first {K V} (eqb : K -> K -> bool) (key : K) (value : V) (xs : list (K * V)) : list (K * V) :=
  match xs with
  | [] => [(key,value)]
  | (k,v) :: rest => if eqb key k then (key,value) :: rest else (k,v) :: update_first eqb key value rest
  end.
Fixpoint update_many {K V} (eqb : K -> K -> bool) (xs : list (K * V)) (keys : list K) (values : list V) : option (list (K * V)) :=
  match keys, values with
  | [], [] => Some xs
  | k :: ks, v :: vs => update_many eqb (update_first eqb k v xs) ks vs
  | _, _ => None
  end.
Fixpoint find_many {K V} (eqb : K -> K -> bool) (xs : list (list (K * V))) (key : K) : option V :=
  match xs with [] => None | x :: rest =>
    match assoc_first eqb key x with Some v => Some v | None => find_many eqb rest key end end.
Fixpoint transpose_width {A} (width : nat) (rows : list (list A)) : list (list A) :=
  match width with
  | O => []
  | S n => (flat_map (fun row => firstn 1 row) rows) :: transpose_width n (map (skipn 1) rows)
  end.
Fixpoint split_byte (separator : ascii) (text : string) : list string :=
  match text with
  | EmptyString => [EmptyString]
  | String c rest =>
      let parts := split_byte separator rest in
      if Ascii.eqb c separator then EmptyString :: parts else
      match parts with [] => [String c EmptyString] | part :: more => String c part :: more end
  end.
Fixpoint starts_with (prefix text : string) : bool :=
  match prefix, text with
  | EmptyString, _ => true
  | String p ps, String c cs => andb (Ascii.eqb p c) (starts_with ps cs)
  | _, _ => false end.
Fixpoint drop_text (n : nat) (text : string) : string :=
  match n, text with S k, String _ rest => drop_text k rest | _, _ => text end.
Definition take_text (n : nat) (text : string) : string := bytes_string (firstn n (string_bytes text)).
Fixpoint remove_spaces (text : string) : string :=
  match text with EmptyString => EmptyString | String c rest =>
    if Ascii.eqb c " "%char then remove_spaces rest else String c (remove_spaces rest) end.

Definition host_error {Call A} (detail : string) : Action Call A :=
  Raise {| error_kind := HostConversion; error_detail := detail |}.
(* OCaml 64-bit int bounds; resource exhaustion is not modeled. *)
Definition host_max : Z := (2 ^ 62 - 1)%Z.
Definition host_min : Z := (- (2 ^ 62))%Z.
Definition fits_host (z : Z) : bool := andb (Z.leb host_min z) (Z.leb z host_max).

Definition digit_value (c : ascii) : option Z :=
  let n := nat_of_ascii c in
  if andb (Nat.leb 48 n) (Nat.leb n 57) then Some (Z.of_nat (n - 48)) else
  if andb (Nat.leb 65 n) (Nat.leb n 70) then Some (Z.of_nat (n - 55)) else
  if andb (Nat.leb 97 n) (Nat.leb n 102) then Some (Z.of_nat (n - 87)) else None.
Fixpoint parse_digits (base acc : Z) (seen : bool) (text : string) : option Z :=
  match text with
  | EmptyString => Some acc
  | String c rest =>
      if Ascii.eqb c "_"%char then (if seen then parse_digits base acc seen rest else None) else
      match digit_value c with
      | Some d => if Z.ltb d base then parse_digits base (acc * base + d)%Z true rest else None
      | None => None end
  end.
Definition parse_unsigned (text : string) : option Z :=
  match text with
  | String "0"%char (String c rest) =>
      if orb (Ascii.eqb c "x"%char) (Ascii.eqb c "X"%char) then parse_digits 16 0 false rest else
      if orb (Ascii.eqb c "o"%char) (Ascii.eqb c "O"%char) then parse_digits 8 0 false rest else
      if orb (Ascii.eqb c "b"%char) (Ascii.eqb c "B"%char) then parse_digits 2 0 false rest else
      parse_digits 10 0 false text
  | _ => parse_digits 10 0 false text end.
Definition parse_integer (text : string) : option Z :=
  match text with
  | String "-"%char rest => option_map Z.opp (parse_unsigned rest)
  | String "+"%char rest => parse_unsigned rest
  | _ => parse_unsigned text end.
