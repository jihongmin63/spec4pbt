(* Pure Wasm SIMD implementation. Apache-2.0 donor provenance is recorded in
   translator/tests/builtins/wasm/PROVENANCE.json. *)
From Coq Require Import ZArith List String Bool.
From ALCoq Require Import Execution.
From ALCoq.Builtins Require Import WasmScalar WasmFloat.
Import ListNotations WasmScalar.
Set Implicit Arguments.
Set Universe Polymorphism.
Open Scope string_scope.
Open Scope Z_scope.
Module WasmVector.
Definition member (op : string) (ops : list string) := existsb (String.eqb op) ops.
Definition lane_width (w : Z) := (w =? 8) || (w =? 16) || (w =? 32) || (w =? 64).
Definition float_width (w : Z) := (w =? 32) || (w =? 64).
Definition indices (w : Z) : list Z := map Z.of_nat (seq 0 (Z.to_nat (128/w))).
Definition lanes (w v : Z) := map (lane w v) (indices w).
Fixpoint pack (w : Z) (xs : list Z) : Z :=
  match xs with [] => 0 | x :: rest => wrap w x + pow2 w * pack w rest end.
Definition map_lanes (w : Z) (f : Z -> Z) (v : Z) := pack w (map f (lanes w v)).
Definition zip_lanes (w : Z) (f : Z -> Z -> Z) (a b : Z) := pack w (map (fun i => f (lane w a i) (lane w b i)) (indices w)).
Fixpoint traverse {A B} (f : A -> Outcome B) (xs : list A) : Outcome (list B) :=
  match xs with [] => Success [] | x :: rest =>
    bind_outcome (f x) (fun y => map_outcome (cons y) (traverse f rest)) end.
Definition valid_vec := valid_word 128.
Definition valid_vectors (xs : list Z) := forallb valid_vec xs.
Definition checked_vec {A} (xs : list Z) (f : Outcome A) : Outcome A :=
  if valid_vectors xs then f else failure HostConversion "v128 operand out of range".
Definition integer_binary_allowed (w : Z) (op : string) :=
  if w =? 8 then member op ["Add";"Sub";"AddSatS";"AddSatU";"SubSatS";"SubSatU";"MinS";"MinU";"MaxS";"MaxU";"AvgrU"] else
  if w =? 16 then member op ["Add";"Sub";"Mul";"AddSatS";"AddSatU";"SubSatS";"SubSatU";"MinS";"MinU";"MaxS";"MaxU";"AvgrU";"Q15MulRSatS";"RelaxedQ15MulRS"] else
  if w =? 32 then member op ["Add";"Sub";"Mul";"MinS";"MinU";"MaxS";"MaxU"] else
  if w =? 64 then member op ["Add";"Sub";"Mul"] else false.
Definition integer_vector_binary (w : Z) (op : string) (shuffle : list nat) (a b : Z) : Outcome Z :=
  if String.eqb op "Shuffle" && negb (forallb machine_nat shuffle) then
    failure HostConversion "shuffle index machine integer overflow" else
  if member op ["Swizzle";"RelaxedSwizzle"] then
    if w =? 8 then Success (pack 8 (map (fun i => if i <? 16 then lane 8 a i else 0) (lanes 8 b))) else unsupported else
  if String.eqb op "Shuffle" then
    if (w =? 8) && Nat.eqb (List.length shuffle) 16 && forallb (fun i => Nat.ltb i 32) shuffle
    then Success (pack 8 (map (fun n => let i := Z.of_nat n in if i <? 16 then lane 8 a i else lane 8 b (i-16)) shuffle)) else unsupported else
  if member op ["NarrowS";"NarrowU"] then
    if (w =? 8) || (w =? 16) then Success (pack w (map (fun x => clamp w (String.eqb op "NarrowS") (signed (w*2) x)) (List.app (lanes (w*2) a) (lanes (w*2) b)))) else unsupported else
  let narrow := w/2 in
  if member op ["ExtMulLowS";"ExtMulHighS";"ExtMulLowU";"ExtMulHighU"] then
    if (w =? 16) || (w =? 32) || (w =? 64) then
      let high := member op ["ExtMulHighS";"ExtMulHighU"] in
      let sign := member op ["ExtMulLowS";"ExtMulHighS"] in
      let offset := if high then 128/w else 0 in
      let extend := fun x => if sign then signed narrow x else x in
      Success (pack w (map (fun i => wrap w (extend (lane narrow a (i+offset))*extend (lane narrow b (i+offset)))) (indices w))) else unsupported else
  if member op ["DotS";"RelaxedDot"] then
    if ((w =? 32) && String.eqb op "DotS") || ((w =? 16) && String.eqb op "RelaxedDot") then
      Success (pack w (map (fun i => wrap w (signed narrow (lane narrow a (2*i))*signed narrow (lane narrow b (2*i)) +
        signed narrow (lane narrow a (2*i+1))*signed narrow (lane narrow b (2*i+1)))) (indices w))) else unsupported else
  if integer_binary_allowed w op then
    map_outcome (pack w) (traverse (fun i => integer_binary w op (lane w a i) (lane w b i)) (indices w)) else unsupported.
Definition integer_vector_convert (w : Z) (op : string) (v : Z) : Outcome Z :=
  if member op ["ExtendLowS";"ExtendLowU";"ExtendHighS";"ExtendHighU";"ExtAddPairwiseS";"ExtAddPairwiseU"] then
    let pairwise := member op ["ExtAddPairwiseS";"ExtAddPairwiseU"] in
    if ((w =? 16) || (w =? 32) || (w =? 64)) && negb ((w =? 64) && pairwise) then
      let sw := w/2 in let sign := member op ["ExtendLowS";"ExtendHighS";"ExtAddPairwiseS"] in
      let cvt := fun i => if sign then signed sw (lane sw v i) else lane sw v i in
      let offset := if member op ["ExtendHighS";"ExtendHighU"] then 128/w else 0 in
      Success (pack w (map (fun i => wrap w (if pairwise then cvt (2*i)+cvt (2*i+1) else cvt (i+offset))) (indices w))) else unsupported else
  if w =? 32 then
    let from64 := member op ["TruncSatSZeroF64x2";"TruncSatUZeroF64x2";"RelaxedTruncSZeroF64x2";"RelaxedTruncUZeroF64x2"] in
    let from32 := member op ["TruncSatSF32x4";"TruncSatUF32x4";"RelaxedTruncSF32x4";"RelaxedTruncUF32x4"] in
    if from64 || from32 then
      let sign := member op ["TruncSatSF32x4";"TruncSatSZeroF64x2";"RelaxedTruncSF32x4";"RelaxedTruncSZeroF64x2"] in
      let sw := if from64 then 64 else 32 in
      map_outcome (pack 32) (traverse (WasmFloat.to_int sw 32 sign true) (lanes sw v)) else unsupported
  else unsupported.
Definition float_vector_convert (w : Z) (op : string) (v : Z) : Outcome Z :=
  if member op ["ConvertSI32x4";"ConvertUI32x4"] && float_width w then
    Success (pack w (map (fun x => WasmFloat.of_int w (if String.eqb op "ConvertSI32x4" then signed 32 x else x))
      (firstn (Z.to_nat (128/w)) (lanes 32 v)))) else
  if (w =? 32) && String.eqb op "DemoteZeroF64x2" then Success (pack 32 (map (WasmFloat.convert 64 32) (lanes 64 v))) else
  if (w =? 64) && String.eqb op "PromoteLowF32x4" then Success (pack 64 (map (WasmFloat.convert 32 64) (firstn 2 (lanes 32 v)))) else unsupported.
Definition bitselect (a b mask : Z) := Z.lor (Z.land a mask) (Z.land b (Z.lxor mask (pow2 128-1))).
Definition replace_lane (w v i x : Z) :=
  let factor := pow2 (w*i) in
  v mod factor + wrap w x * factor + v / (factor*pow2 w) * (factor*pow2 w).
Definition eval_vtestop (w : Z) (v : Z) : Outcome nat := checked_vec [v]
  (if lane_width w then Success (bool_nat (forallb (fun x => negb (x =? 0)) (lanes w v))) else unsupported).
Definition eval_vunop (w : Z) (floating : bool) (op : string) (v : Z) : Outcome Z := checked_vec [v]
  (if floating then
    if float_width w && member op ["abs";"neg";"sqrt";"ceil";"floor";"trunc";"nearest"]
    then Success (map_lanes w (WasmFloat.unary w op) v) else unsupported
   else if lane_width w && member op ["Abs";"Neg";"Popcnt"] && (negb (String.eqb op "Popcnt") || (w =? 8))
    then map_outcome (pack w) (traverse (integer_unary w op 0) (lanes w v)) else unsupported).
Definition eval_vrelop (w : Z) (floating : bool) (op : string) (a b : Z) : Outcome Z := checked_vec [a;b]
  (if floating then
    if float_width w && member op ["eq";"ne";"lt";"le";"gt";"ge"] then
      Success (zip_lanes w (fun x y => if WasmFloat.compare w op x y then pow2 w-1 else 0) a b) else unsupported
   else if lane_width w && negb ((w =? 64) && member op ["LtU";"LeU";"GtU";"GeU"]) then
    map_outcome (pack w) (traverse (fun i => map_outcome (fun (yes : bool) => if yes then pow2 w-1 else 0)
      (integer_compare w op (lane w a i) (lane w b i))) (indices w)) else unsupported).
Definition eval_vbinop (w : Z) (floating : bool) (op : string) (shuffle : list nat) (a b : Z) : Outcome Z := checked_vec [a;b]
  (if floating then
    if float_width w && member op ["add";"sub";"mul";"div";"min";"max";"pmin";"pmax";"relaxedmin";"relaxedmax"]
    then Success (zip_lanes w (WasmFloat.binary w op) a b) else unsupported
   else integer_vector_binary w op shuffle a b).
Definition eval_vternop (w : Z) (floating : bool) (op : string) (a b c : Z) : Outcome Z := checked_vec [a;b;c]
  (if floating then
    if float_width w && member op ["RelaxedMadd";"RelaxedNmadd"] then
      Success (pack w (map (fun i => let x := lane w a i in
        WasmFloat.fma w (if String.eqb op "RelaxedNmadd" then Z.lxor x (pow2 (w-1)) else x) (lane w b i) (lane w c i)) (indices w))) else unsupported
   else if lane_width w && String.eqb op "RelaxedLaneselect" then Success (bitselect a b c) else
    if (w =? 32) && String.eqb op "RelaxedDotAdd" then
      Success (pack 32 (map (fun i => wrap 32 (signed 32 (lane 32 c i) + fold_right Z.add 0
        (map (fun j => signed 8 (lane 8 a (4*i+j)) * signed 8 (lane 8 b (4*i+j))) [0;1;2;3]))) [0;1;2;3])) else unsupported).
Definition eval_vcvtop (w : Z) (floating : bool) (op : string) (v : Z) : Outcome Z := checked_vec [v]
  (if floating then float_vector_convert w op v else integer_vector_convert w op v).
Definition eval_vshiftop (w : Z) (op : string) (v n : Z) : Outcome Z := checked_vec [v]
  (if valid_word 32 n then
    if lane_width w && member op ["Shl";"ShrS";"ShrU"] then
      (* The native SIMD shift count is a u32, masked to lane width before use. *)
      map_outcome (pack w) (traverse (fun x => integer_binary w op x (n mod w)) (lanes w v)) else unsupported
   else failure HostConversion "SIMD shift is not u32").
Definition eval_vbitmaskop (w : Z) (v : Z) : Outcome Z := checked_vec [v]
  (if lane_width w then Success (fold_right Z.add 0 (map (fun i => (lane w v i / pow2 (w-1))*pow2 i) (indices w))) else unsupported).
Definition eval_vvtestop (v : Z) : Outcome nat := checked_vec [v] (Success (bool_nat (negb (v =? 0)))).
Definition eval_vvunop (v : Z) : Outcome Z := checked_vec [v] (Success (Z.lxor v (pow2 128-1))).
Definition eval_vvbinop (op : string) (a b : Z) : Outcome Z := checked_vec [a;b]
  (if String.eqb op "And" then Success (Z.land a b) else
   if String.eqb op "Or" then Success (Z.lor a b) else
   if String.eqb op "Xor" then Success (Z.lxor a b) else
   if String.eqb op "AndNot" then Success (Z.land a (Z.lxor b (pow2 128-1))) else unsupported).
Definition eval_vvternop (a b c : Z) : Outcome Z := checked_vec [a;b;c] (Success (bitselect a b c)).
Definition eval_vsplatop (w source_width : Z) (x : Z) : Outcome Z :=
  if valid_word source_width x && lane_width w then Success (pack w (repeat x (Z.to_nat (128/w))))
  else failure HostConversion "invalid SIMD splat operand".
Definition machine_index (i : Z) := (-4611686018427387904 <=? i) && (i <=? machine_max).
Definition eval_vextractop (w : Z) (sign : bool) (v i : Z) : Outcome Z := checked_vec [v]
  (if machine_index i then
    if lane_width w && (0 <=? i) && (i <? 128/w) then
      let x := lane w v i in Success (if sign && (w <? 32) then wrap 32 (signed w x) else x)
    else failure ExternalAbort "SIMD extraction lane out of bounds"
   else failure HostConversion "SIMD extraction lane machine integer overflow").
Definition eval_vreplaceop (w source_width : Z) (v i x : Z) : Outcome Z := checked_vec [v]
  (if machine_index i && valid_word source_width x then
    if lane_width w then Success (if (0 <=? i) && (i <? 128/w) then replace_lane w v i x else v) else unsupported
   else failure HostConversion "invalid SIMD replacement operand").
End WasmVector.
