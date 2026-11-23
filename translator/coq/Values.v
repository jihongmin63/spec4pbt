From Coq Require Import String Ascii List Bool ZArith Arith DecimalString.
Import ListNotations.
Set Implicit Arguments.
Set Universe Polymorphism.
Open Scope string_scope.

(* The relation lowering emits the constructor form for a natural successor.
   This is the exact arithmetic identity used by that normalization. *)
Lemma nat_add_one_as_successor : forall n : nat, Nat.add n 1 = S n.
Proof. intro n; induction n; simpl; congruence. Qed.

(* Equality, source structural order and source printing are separate contracts.
   A polymorphic caller supplies all three rather than equating functions. *)
Record ValueOps (A : Type) := {
  equal_value : A -> A -> bool;
  compare_value : A -> A -> comparison;
  print_value : nat -> A -> string;
  unparse_value : A -> option string
}.
Arguments equal_value {A} _ _ _.
Arguments compare_value {A} _ _ _.
Arguments print_value {A} _ _ _.
Arguments unparse_value {A} _ _.

Definition subtract_nat (x y : nat) : Z := (Z.of_nat x - Z.of_nat y)%Z.
Definition divide_int (x y : Z) : option Z :=
  if Z.eqb y 0 then None else Some (Z.quot x y).
Definition remainder_int (x y : Z) : option Z :=
  if Z.eqb y 0 then None else Some (Z.rem x y).
Definition divide_nat (x y : nat) : option nat :=
  if Nat.eqb y 0 then None else Some (Nat.div x y).
Definition remainder_nat (x y : nat) : option nat :=
  if Nat.eqb y 0 then None else Some (Nat.modulo x y).

Fixpoint compare_text (x y : string) : comparison :=
  match x, y with
  | EmptyString, EmptyString => Eq
  | EmptyString, _ => Lt
  | _, EmptyString => Gt
  | String a xs, String b ys =>
      match Nat.compare (nat_of_ascii a) (nat_of_ascii b) with
      | Eq => compare_text xs ys | c => c end
  end.
Fixpoint equal_list {A} (eqb : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => andb (eqb x y) (equal_list eqb xs ys)
  | _, _ => false end.
Fixpoint compare_list {A} (cmp : A -> A -> comparison) (xs ys : list A) : comparison :=
  match xs, ys with
  | [], [] => Eq | [], _ => Lt | _, [] => Gt
  | x :: xs, y :: ys => match cmp x y with Eq => compare_list cmp xs ys | c => c end
  end.
Definition equal_option {A} (eqb : A -> A -> bool) (x y : option A) : bool :=
  match x, y with None, None => true | Some a, Some b => eqb a b | _, _ => false end.
Definition compare_option {A} (cmp : A -> A -> comparison) (x y : option A) : comparison :=
  match x, y with None, None => Eq | None, _ => Lt | _, None => Gt | Some a, Some b => cmp a b end.
Definition index_list {A} (xs : list A) (n : nat) : option A := nth_error xs n.
Definition host_int_max : Z := 4611686018427387903%Z.
(* Both operands have passed Bigint.to_int_exn. On the pinned 63-bit OCaml
   runtime their nonnegative sum either stays in range or wraps below zero. *)
Definition host_sum_overflows (start count : Z) : bool :=
  Z.ltb host_int_max (start + count).
Definition slice_sum_overflows (start count : nat) : bool :=
  host_sum_overflows (Z.of_nat start) (Z.of_nat count).
(* Once both indices fit OCaml int, an overflowing sum wraps below zero.
   The native list branch then selects no elements and succeeds. *)
Definition slice_list_at_limit {A} (limit : Z) (xs : list A) (start count : nat) : option (list A) :=
  if Z.ltb limit (Z.add (Z.of_nat start) (Z.of_nat count)) then Some []
  else if Nat.leb (start + count) (List.length xs)
       then Some (firstn count (skipn start xs)) else None.
Definition slice_list {A} (xs : list A) (start count : nat) : option (list A) :=
  slice_list_at_limit host_int_max xs start count.
Definition splice_list {A} (xs : list A) (start count : nat) (replacement : list A) : option (list A) :=
  if slice_sum_overflows start count then
    if Nat.eqb (List.length replacement) count then Some xs else None
  else if andb (Nat.leb (start + count) (List.length xs)) (Nat.eqb (List.length replacement) count)
       then Some (List.app (firstn start xs) (List.app replacement (skipn (start + count) xs))) else None.
Fixpoint string_bytes (s : string) : list ascii :=
  match s with EmptyString => [] | String c rest => c :: string_bytes rest end.
Fixpoint bytes_string (s : list ascii) : string :=
  match s with [] => EmptyString | c :: rest => String c (bytes_string rest) end.
Definition index_text (s : string) (n : nat) : option string :=
  match nth_error (string_bytes s) n with None => None | Some c => Some (String c EmptyString) end.
Definition slice_text (s : string) (start count : nat) : option string :=
  (* The lowering checks slice_sum_overflows first and raises the native
     Invalid_argument. This option handles the ordinary bounds/result branch. *)
  let bytes := string_bytes s in
  if slice_sum_overflows start count then None
  else if Nat.leb (start + count) (List.length bytes)
  then Some (bytes_string (firstn count (skipn start bytes))) else None.
Definition splice_text (s : string) (start count : nat) (replacement : string) : option string :=
  let bytes := string_bytes s in
  if slice_sum_overflows start count then None
  else if andb (Nat.leb (start + count) (List.length bytes)) (Nat.eqb (String.length replacement) count)
  then Some (bytes_string (List.app (firstn start bytes)
    (List.app (string_bytes replacement) (skipn (start + count) bytes)))) else None.
(* Native text update checks replacement length before calling String.sub.
   Do not turn a length mismatch into an uncaught host exception. *)
Definition text_splice_host_error (start count : nat) (replacement : string) : bool :=
  andb (slice_sum_overflows start count) (Nat.eqb (String.length replacement) count).
Definition print_nat (n : nat) : string := DecimalString.NilZero.string_of_uint (Nat.to_uint n).
Definition print_int (z : Z) : string :=
  String.append (if Z.ltb z 0 then "-" else "+")
                (print_nat (Z.to_nat (Z.abs z))).
Fixpoint indent (n : nat) : string :=
  match n with O => "" | S k => String.append "  " (indent k) end.
Fixpoint join_text (separator : string) (items : list string) : string :=
  match items with [] => "" | [x] => x | x :: xs => String.append x (String.append separator (join_text separator xs)) end.
Definition print_option {A} (print : nat -> A -> string) (level : nat) (x : option A) : string :=
  match x with None => "None" | Some a => String.append "Some(" (String.append (print (S level) a) ")") end.
Definition newline : string := String (ascii_of_nat 10) EmptyString.
Definition print_list {A} (print : nat -> A -> string) (level : nat) (xs : list A) : string :=
  match xs with
  | [] => "[]"
  | _ => String.append "[" (String.append newline
      (String.append (join_text (String.append "," newline)
         (map (fun x => String.append (indent (S level)) (print (S level) x)) xs))
         (String.append newline (String.append (indent level) "]"))))
  end.
Fixpoint traverse_option {A B} (f : A -> option B) (xs : list A) : option (list B) :=
  match xs with
  | [] => Some []
  | x :: xs => match f x, traverse_option f xs with
               | Some y, Some ys => Some (y :: ys) | _, _ => None end
  end.
Definition nat_ops : ValueOps nat :=
  {| equal_value := Nat.eqb; compare_value := Nat.compare; print_value := fun _ => print_nat; unparse_value := fun n => Some (print_nat n) |}.
Definition int_ops : ValueOps Z :=
  {| equal_value := Z.eqb; compare_value := Z.compare; print_value := fun _ => print_int; unparse_value := fun z =>
       Some (String.append (if Z.ltb z 0 then "-" else "") (print_nat (Z.to_nat (Z.abs z)))) |}.
Definition bool_ops : ValueOps bool :=
  {| equal_value := Bool.eqb;
     compare_value := fun a b => if Bool.eqb a b then Eq else if a then Gt else Lt;
     print_value := fun _ a => if a then "true" else "false";
     unparse_value := fun a => Some (if a then "true" else "false") |}.
Definition decimal_digit (n : nat) : ascii := ascii_of_nat (48 + n).
Definition escaped_byte (c : ascii) : string :=
  let n := nat_of_ascii c in
  if Nat.eqb n 34 then String (ascii_of_nat 92) (String c "") else
  if Nat.eqb n 92 then String c (String c "") else
  if Nat.eqb n 10 then String (ascii_of_nat 92) "n" else
  if Nat.eqb n 9 then String (ascii_of_nat 92) "t" else
  if Nat.eqb n 13 then String (ascii_of_nat 92) "r" else
  if Nat.eqb n 8 then String (ascii_of_nat 92) "b" else
  if andb (Nat.leb 32 n) (Nat.leb n 126) then String c "" else
  String (ascii_of_nat 92)
    (String (decimal_digit (n / 100))
      (String (decimal_digit ((n / 10) mod 10)) (String (decimal_digit (n mod 10)) ""))).
Fixpoint escape_text (s : string) : string :=
  match s with EmptyString => "" | String c rest => String.append (escaped_byte c) (escape_text rest) end.
Definition print_text (s : string) : string :=
  escape_text s.
Definition text_ops : ValueOps string :=
  {| equal_value := String.eqb; compare_value := compare_text; print_value := fun _ => print_text; unparse_value := fun s => Some (escape_text s) |}.
Definition unit_ops : ValueOps unit :=
  {| equal_value := fun _ _ => true; compare_value := fun _ _ => Eq; print_value := fun _ _ => "()"; unparse_value := fun _ => Some "()" |}.
Definition list_ops {A} (ops : ValueOps A) : ValueOps (list A) :=
  {| equal_value := equal_list (equal_value ops);
     compare_value := compare_list (compare_value ops);
     print_value := print_list (print_value ops);
     unparse_value := fun xs => option_map (join_text " ") (traverse_option (unparse_value ops) xs) |}.
Definition option_ops {A} (ops : ValueOps A) : ValueOps (option A) :=
  {| equal_value := equal_option (equal_value ops);
     compare_value := compare_option (compare_value ops);
     print_value := print_option (print_value ops);
     unparse_value := fun x => match x with None => Some "" | Some v => unparse_value ops v end |}.
Definition pair_ops {A B} (a : ValueOps A) (b : ValueOps B) : ValueOps (A * B) :=
  {| equal_value := fun x y => andb (equal_value a (fst x) (fst y)) (equal_value b (snd x) (snd y));
     compare_value := fun x y => match compare_value a (fst x) (fst y) with
                                | Eq => compare_value b (snd x) (snd y) | c => c end;
     print_value := fun level x => String.append "(" (String.append (print_value a (S level) (fst x))
                        (String.append ", " (String.append (print_value b (S level) (snd x)) ")")));
     unparse_value := fun x => match unparse_value a (fst x), unparse_value b (snd x) with
       | Some av, Some bv => Some (String.append "(" (String.append av (String.append ", " (String.append bv ")"))))
       | _, _ => None end |}.
Definition product_ops := @pair_ops.
Arguments product_ops {A B} _ _.
