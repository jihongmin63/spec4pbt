(* Wasm numeric support, ported from wasm-ntt 4773b2b7abe56e61f279ec2340ac0d3c836b5033
   via donor 16142ff23b30611a3fba1bb0ceb0dd7928187d58. Apache-2.0;
   see translator/tests/builtins/wasm/PROVENANCE.json and LICENSE. *)
From Coq Require Import ZArith List String Ascii Bool.
From ALCoq Require Import Execution Values.
Import ListNotations.
Set Implicit Arguments.
Set Implicit Arguments.
Set Universe Polymorphism.
Open Scope string_scope.
Open Scope Z_scope.
Module WasmScalar.
Definition pow2 (n : Z) : Z := 2 ^ n.
Definition wrap (width value : Z) : Z := value mod pow2 width.
Definition signed (width value : Z) : Z :=
  let v := wrap width value in if v <? pow2 (width - 1) then v else v - pow2 width.
Definition valid_word (width value : Z) : bool := (0 <=? value) && (value <? pow2 width).
Definition bool_nat (b : bool) : nat := if b then 1%nat else 0%nat.
Definition failure {A} (kind : ErrorKind) (detail : string) : Outcome A :=
  Error {| error_kind := kind; error_detail := detail |}.
Definition lift {Call A} (result : Outcome A) : Action Call A :=
  match result with Success x => Return x | Unmatch => Unmatched | Error e => Raise e end.
Definition map_outcome {A B} (f : A -> B) (x : Outcome A) : Outcome B :=
  match x with Success a => Success (f a) | Unmatch => Unmatch | Error e => Error e end.
Definition bind_outcome {A B} (x : Outcome A) (f : A -> Outcome B) : Outcome B :=
  match x with Success a => f a | Unmatch => Unmatch | Error e => Error e end.
Definition checked {A} (ok : bool) (value : A) : Outcome A :=
  if ok then Success value else failure HostConversion "invalid Wasm numeric representation".
Definition unsupported {A} : Outcome A := failure StructureError "invalid opcode or operand type".
Definition scalar_binary (width : Z) (op : string) (a b : nat) : nat :=
  Z.to_nat (wrap width (if String.eqb op "add" then Z.of_nat a + Z.of_nat b
    else if String.eqb op "sub" then Z.of_nat a - Z.of_nat b else Z.of_nat a * Z.of_nat b)).
(* Pinned wasm-ntt deliberately saturates positive lsl_ counts at 4096. *)
Definition lsl_ (value count : Z) : Z := Z.shiftl value (Z.min 4096 (Z.max 0 count)).
Definition byte_of_i32 (n : nat) := Z.to_nat (wrap 8 (Z.of_nat n)).
Definition i31_of_i32 (n : nat) := Z.to_nat (wrap 31 (Z.of_nat n)).
Definition i32_add := scalar_binary 32 "add".
Definition i32_sub := scalar_binary 32 "sub".
Definition i32_mul := scalar_binary 32 "mul".
Definition i64_add := scalar_binary 64 "add".
Definition i64_sub := scalar_binary 64 "sub".
Definition i64_mul := scalar_binary 64 "mul".
Definition i32_eqz (n : nat) := bool_nat (Nat.eqb n 0).
Definition i64_eqz := i32_eqz.
Definition i32_gt_u (a b : nat) := bool_nat (Nat.ltb b a).
Definition i32_le_u (a b : nat) := bool_nat (Nat.leb a b).
Definition i64_le_u := i32_le_u.
Definition i32_le_s (a b : nat) := bool_nat (signed 32 (Z.of_nat a) <=? signed 32 (Z.of_nat b)).
Definition i32_ne (a b : nat) := bool_nat (negb (Nat.eqb a b)).
Definition i32_wrap_i64 (n : nat) := Z.to_nat (wrap 32 (Z.of_nat n)).
Definition extend_s (src dst : Z) (n : nat) := Z.to_nat (wrap dst (signed src (Z.of_nat n))).
Definition i32_extend_i8_s := extend_s 8 32.
Definition i32_extend_i16_s := extend_s 16 32.
Definition i31_get_s := extend_s 31 32.
Fixpoint decode_bytes (bytes : list nat) : Z :=
  match bytes with [] => 0 | b :: bs => Z.of_nat b + 256 * decode_bytes bs end.
Definition valid_bytes (bytes : list nat) : bool := forallb (fun b => Nat.ltb b 256) bytes.
Definition lane (width value index : Z) : Z := (value / pow2 (width * index)) mod pow2 width.
Definition encode_bytes (count : nat) (value : Z) : list nat :=
  map (fun i => Z.to_nat (lane 8 value (Z.of_nat i))) (seq 0 count).
Definition bytes_of_i32 (n : nat) : list nat := encode_bytes 4 (Z.of_nat n).
(* Native i32/i64_of_bytes accept arbitrary natural elements; no Char.chr conversion. *)
Definition i32_of_bytes (bytes : list nat) : nat := Z.to_nat (wrap 32 (decode_bytes bytes)).
Definition i64_of_bytes (bytes : list nat) : nat := Z.to_nat (wrap 64 (decode_bytes bytes)).
Definition v128_of_bytes (bytes : list nat) : Outcome nat :=
  checked (valid_bytes bytes) (Z.to_nat (decode_bytes bytes)).
Definition machine_max : Z := 4611686018427387903.
Definition machine_nat (n : nat) := Z.of_nat n <=? machine_max.
Definition zero_bytes (n : nat) : Outcome (list nat) := checked (machine_nat n) (repeat 0%nat n).
(* repeat_byte preserves its input byte value, including noncanonical natural aliases. *)
Definition repeat_byte (b n : nat) : Outcome (list nat) := checked (machine_nat n) (repeat b n).
Definition slice_bytes (bytes : list nat) (offset count : nat) : Outcome (list nat) :=
  if machine_nat offset && machine_nat count then
    if Nat.leb (offset + count) (List.length bytes)
    then Success (firstn count (skipn offset bytes))
    else failure ExternalAbort "slice_bytes out of bounds"
  else failure HostConversion "slice_bytes machine integer overflow".
Definition replace_bytes (bytes : list nat) (offset : nat) (replacement : list nat) : Outcome (list nat) :=
  if machine_nat offset then
    if Nat.leb (offset + List.length replacement) (List.length bytes)
    then Success (List.app (firstn offset bytes) (List.app replacement (skipn (offset + List.length replacement) bytes)))
    else failure ExternalAbort "replace_bytes out of bounds"
  else failure HostConversion "replace_bytes machine integer overflow".
(* Coq strings, like the donor OCaml strings, contain bytes already encoded as UTF-8. *)
Definition bytes_of_text (text : string) : list nat := map nat_of_ascii (string_bytes text).
Definition clamp (width : Z) (sign : bool) (x : Z) : Z :=
  let lo := if sign then -pow2 (width - 1) else 0 in
  let hi := if sign then pow2 (width - 1) - 1 else pow2 width - 1 in
  wrap width (Z.max lo (Z.min hi x)).
Fixpoint leading_zeroes (bits : list Z) : nat :=
  match bits with [] => 0%nat | x :: xs => if x =? 0 then S (leading_zeroes xs) else 0%nat end.
Definition integer_unary (width : Z) (op : string) (pack_width x : Z) : Outcome Z :=
  if valid_word width x then
  let bits := map (fun i => lane 1 x (Z.of_nat i)) (seq 0 (Z.to_nat width)) in
  if String.eqb op "Clz" then Success (Z.of_nat (leading_zeroes (rev bits))) else
  if String.eqb op "Ctz" then Success (Z.of_nat (leading_zeroes bits)) else
  if String.eqb op "Popcnt" then Success (fold_right Z.add 0 bits) else
  if String.eqb op "ExtendS" then
    if (0 <? pack_width) && (pack_width <=? width) then Success (wrap width (signed pack_width x)) else
    (* Source admits Pack64 for I32. The pinned OCaml runtime evaluates its
       native shift count -32 as zero; preserve that observed donor behavior. *)
    if (width =? 32) && (pack_width =? 64) then Success x else unsupported else
  if String.eqb op "Abs" then Success (wrap width (Z.abs (signed width x))) else
  if String.eqb op "Neg" then Success (wrap width (-x)) else unsupported
  else failure HostConversion "integer operand out of range".
Definition integer_binary (width : Z) (op : string) (a b : Z) : Outcome Z :=
  if valid_word width a && valid_word width b then
  let sa := signed width a in let sb := signed width b in let shift := b mod width in
  if String.eqb op "Add" then Success (wrap width (a+b)) else
  if String.eqb op "Sub" then Success (wrap width (a-b)) else
  if String.eqb op "Mul" then Success (wrap width (a*b)) else
  if String.eqb op "DivS" then
    if (b =? 0) || ((sa =? -pow2 (width-1)) && (sb =? -1)) then failure NumericTrap "integer divide trap"
    else Success (wrap width (Z.quot sa sb)) else
  if String.eqb op "DivU" then if b =? 0 then failure NumericTrap "integer divide by zero" else Success (a/b) else
  if String.eqb op "RemS" then if b =? 0 then failure NumericTrap "integer remainder by zero" else Success (wrap width (Z.rem sa sb)) else
  if String.eqb op "RemU" then if b =? 0 then failure NumericTrap "integer remainder by zero" else Success (a mod b) else
  if String.eqb op "And" then Success (Z.land a b) else
  if String.eqb op "Or" then Success (Z.lor a b) else
  if String.eqb op "Xor" then Success (Z.lxor a b) else
  if String.eqb op "Shl" then Success (wrap width (Z.shiftl a shift)) else
  if String.eqb op "ShrU" then Success (Z.shiftr a shift) else
  if String.eqb op "ShrS" then Success (wrap width (Z.shiftr sa shift)) else
  if String.eqb op "Rotl" then Success (wrap width (Z.lor (Z.shiftl a shift) (Z.shiftr a (width-shift)))) else
  if String.eqb op "Rotr" then Success (wrap width (Z.lor (Z.shiftr a shift) (Z.shiftl a (width-shift)))) else
  if String.eqb op "MinS" then Success (wrap width (Z.min sa sb)) else
  if String.eqb op "MinU" then Success (Z.min a b) else
  if String.eqb op "MaxS" then Success (wrap width (Z.max sa sb)) else
  if String.eqb op "MaxU" then Success (Z.max a b) else
  if String.eqb op "AvgrU" then Success ((a+b+1)/2) else
  if String.eqb op "AddSatS" then Success (clamp width true (sa+sb)) else
  if String.eqb op "AddSatU" then Success (clamp width false (a+b)) else
  if String.eqb op "SubSatS" then Success (clamp width true (sa-sb)) else
  if String.eqb op "SubSatU" then Success (clamp width false (a-b)) else
  if String.eqb op "Q15MulRSatS" || String.eqb op "RelaxedQ15MulRS" then Success (clamp 16 true (Z.shiftr (sa*sb+16384) 15)) else unsupported
  else failure HostConversion "integer operand out of range".
Definition integer_compare (width : Z) (op : string) (a b : Z) : Outcome bool :=
  if valid_word width a && valid_word width b then
  let sa := signed width a in let sb := signed width b in
  if String.eqb op "Eq" then Success (a =? b) else
  if String.eqb op "Ne" then Success (negb (a =? b)) else
  if String.eqb op "LtS" then Success (sa <? sb) else
  if String.eqb op "LtU" then Success (a <? b) else
  if String.eqb op "GtS" then Success (sb <? sa) else
  if String.eqb op "GtU" then Success (b <? a) else
  if String.eqb op "LeS" then Success (sa <=? sb) else
  if String.eqb op "LeU" then Success (a <=? b) else
  if String.eqb op "GeS" then Success (sb <=? sa) else
  if String.eqb op "GeU" then Success (b <=? a) else unsupported
  else failure HostConversion "integer operand out of range".
End WasmScalar.
