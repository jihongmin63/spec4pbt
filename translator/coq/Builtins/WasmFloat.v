(* Exact rational/bit port of donor SpecTecWasmFloat and wasm-ntt Fxx.
   Apache-2.0; provenance and donor license in tests/builtins/wasm/. *)
From Coq Require Import ZArith String Bool List.
From ALCoq Require Import Execution.
From ALCoq.Builtins Require Import WasmScalar.
Import WasmScalar.
Set Implicit Arguments.
Set Universe Polymorphism.
Open Scope string_scope.
Open Scope Z_scope.
Module WasmFloat.
Definition mantissa (width : Z) := if width =? 32 then 23 else 52.
Definition exponent (width : Z) := if width =? 32 then 8 else 11.
Definition bias (width : Z) := pow2 (exponent width - 1) - 1.
Definition sign_mask (width : Z) := pow2 (width-1).
Definition infinity (width : Z) := (pow2 (exponent width)-1) * pow2 (mantissa width).
Definition quiet_nan (width : Z) := infinity width + pow2 (mantissa width-1).
Definition magnitude (width bits : Z) := bits mod sign_mask width.
Definition negative (width bits : Z) := (bits / sign_mask width) mod 2 =? 1.
Definition is_nan (width bits : Z) := infinity width <? magnitude width bits.
Definition is_inf (width bits : Z) := magnitude width bits =? infinity width.
Definition is_zero (width bits : Z) := magnitude width bits =? 0.
Definition signed_bits (width : Z) (sign : bool) (mag : Z) := (if sign then sign_mask width else 0) + mag.
Definition quiet (width bits : Z) := Z.lor bits (quiet_nan width).
Definition binary_nan (width x y : Z) := quiet width (if is_nan width x then x else if is_nan width y then y else quiet_nan width).
Definition fraction (width bits : Z) : Z * Z :=
  let m := mantissa width in let mag := magnitude width bits in
  let e := mag / pow2 m in let f := mag mod pow2 m in
  let significand := if e =? 0 then f else pow2 m + f in
  let power := (if e =? 0 then 1 else e) - bias width - m in
  if 0 <=? power then (significand * pow2 power, 1) else (significand, pow2 (-power)).
Definition ratio_log2 (n d : Z) :=
  let estimate := Z.log2 n - Z.log2 d in
  let below := if 0 <=? estimate then n <? d * pow2 estimate else n * pow2 (-estimate) <? d in
  if below then estimate-1 else estimate.
Definition scaled_ratio (n d unit_power : Z) : Z * Z :=
  if 0 <=? unit_power then (n, d * pow2 unit_power) else (n * pow2 (-unit_power), d).
Definition round_ratio (n d : Z) :=
  let q := n/d in let r := n mod d in
  if (d <? 2*r) || ((2*r =? d) && (q mod 2 =? 1)) then q+1 else q.
Definition pack_rounded (width : Z) (sign : bool) (significand unit_power : Z) :=
  let m := mantissa width in
  let '(s,power) := if pow2 (m+1) <=? significand then (significand/2,unit_power+1) else (significand,unit_power) in
  let raw_exponent := power + m + bias width in
  let mag := if s <? pow2 m then s else
    if pow2 (exponent width)-1 <=? raw_exponent then infinity width else raw_exponent * pow2 m + (s-pow2 m) in
  signed_bits width sign mag.
Definition of_ratio (width : Z) (sign : bool) (n d : Z) :=
  if n =? 0 then signed_bits width sign 0 else
  let m := mantissa width in let min_power := 1-bias width-m in
  let unit_power := Z.max (ratio_log2 n d - m) min_power in
  let '(a,b) := scaled_ratio n d unit_power in
  pack_rounded width sign (round_ratio a b) unit_power.
Definition convert (src dst bits : Z) :=
  if src =? dst then bits else
  let sign := negative src bits in
  if is_nan src bits then
    let payload := magnitude src bits mod pow2 (mantissa src) in
    let mapped := if mantissa src <=? mantissa dst
      then payload * pow2 (mantissa dst-mantissa src) else payload / pow2 (mantissa src-mantissa dst) in
    signed_bits dst sign (Z.lor (quiet_nan dst) mapped)
  else if is_inf src bits then signed_bits dst sign (infinity dst)
  else let '(n,d) := fraction src bits in of_ratio dst sign n d.
Definition compare (width : Z) (op : string) (x y : Z) : bool :=
  let nan := is_nan width x || is_nan width y in
  let equal := (x =? y) || (is_zero width x && is_zero width y) in
  let less := if equal then false else
    if xorb (negative width x) (negative width y) then negative width x else
    if negative width x then magnitude width y <? magnitude width x else magnitude width x <? magnitude width y in
  if String.eqb op "ne" then nan || negb equal else
  if nan then false else
  if String.eqb op "eq" then equal else
  if String.eqb op "lt" then less else
  if String.eqb op "le" then less || equal else
  if String.eqb op "gt" then negb less && negb equal else
  if String.eqb op "ge" then negb less else false.
Definition finite_arithmetic (width : Z) (op : string) (x y : Z) :=
  let '(nx,dx) := fraction width x in let '(ny,dy) := fraction width y in
  let sx := negative width x in let sy := xorb (negative width y) (String.eqb op "sub") in
  let intermediate := if width =? 32 then 64 else width in
  let result := if String.eqb op "mul" then of_ratio intermediate (xorb sx sy) (nx*ny) (dx*dy) else
    if String.eqb op "div" then of_ratio intermediate (xorb sx sy) (nx*dy) (dx*ny) else
    let a := if sx then -(nx*dy) else nx*dy in
    let b := if sy then -(ny*dx) else ny*dx in let sum := a+b in
    of_ratio intermediate (if sum =? 0 then sx && sy else sum <? 0) (Z.abs sum) (dx*dy) in
  convert intermediate width result.
Definition binary (width : Z) (op : string) (x y : Z) :=
  let op := if String.eqb op "relaxedmin" then "min" else if String.eqb op "relaxedmax" then "max" else op in
  if String.eqb op "pmin" then (if compare width "lt" y x then y else x) else
  if String.eqb op "pmax" then (if compare width "lt" x y then y else x) else
  if String.eqb op "copysign" then signed_bits width (negative width y) (magnitude width x) else
  if is_nan width x || is_nan width y then binary_nan width x y else
  if String.eqb op "min" then
    if compare width "eq" x y then Z.lor x y else if compare width "lt" x y then x else y else
  if String.eqb op "max" then
    if compare width "eq" x y then Z.land x y else if compare width "gt" x y then x else y else
  let sx := negative width x in let sy := xorb (negative width y) (String.eqb op "sub") in
  let ix := is_inf width x in let iy := is_inf width y in
  let zx := is_zero width x in let zy := is_zero width y in
  if String.eqb op "mul" then
    if (ix && zy) || (iy && zx) then quiet_nan width else
    if ix || iy then signed_bits width (xorb sx sy) (infinity width) else finite_arithmetic width op x y else
  if String.eqb op "div" then
    if (ix && iy) || (zx && zy) then quiet_nan width else
    if ix || zy then signed_bits width (xorb sx sy) (infinity width) else
    if iy then signed_bits width (xorb sx sy) 0 else finite_arithmetic width op x y else
  if ix && iy && xorb sx sy then quiet_nan width else
  if ix then x else if iy then signed_bits width sy (infinity width) else finite_arithmetic width op x y.
Definition sqrt_rounded (width n d : Z) :=
  if n =? 0 then 0 else
  let m := mantissa width in let min_power := 1-bias width-m in
  let unit_power := Z.max (Z.div (ratio_log2 n d) 2 - m) min_power in
  let '(a,b) := scaled_ratio n d (2*unit_power) in
  let q := Z.sqrt (a/b) in let midpoint := b * (2*q+1)^2 in
  let rounded := if (midpoint <? 4*a) || ((4*a =? midpoint) && (q mod 2 =? 1)) then q+1 else q in
  pack_rounded width false rounded unit_power.
Definition unary (width : Z) (op : string) (x : Z) :=
  if String.eqb op "abs" then magnitude width x else
  if String.eqb op "neg" then Z.lxor x (sign_mask width) else
  if is_nan width x then quiet width x else if is_zero width x then x else
  if String.eqb op "sqrt" then
    if negative width x then quiet_nan width else if is_inf width x then x else
    let '(n,d) := fraction width x in let intermediate := if width =? 32 then 64 else width in
    convert intermediate width (sqrt_rounded intermediate n d) else
  if is_inf width x then x else
  let '(n,d) := fraction width x in let sign := negative width x in
  let q := n/d in let remainder := n mod d in
  let rounded := if String.eqb op "nearest" then round_ratio n d else
    if (String.eqb op "ceil" && negb sign) || (String.eqb op "floor" && sign)
      then q + (if remainder =? 0 then 0 else 1) else q in
  of_ratio width sign rounded 1.
Definition of_int (width value : Z) := of_ratio width (value <? 0) (Z.abs value) 1.
Definition to_int (src dst : Z) (sign saturated : bool) (bits : Z) : Outcome Z :=
  let modulus := pow2 dst in
  let lower := if sign then -pow2 (dst-1) else 0 in
  let upper := if sign then pow2 (dst-1)-1 else modulus-1 in
  if is_nan src bits then if saturated then Success 0 else failure NumericTrap "invalid float to integer conversion" else
  if is_inf src bits then
    if saturated then Success ((if negative src bits then lower else upper) mod modulus)
    else failure NumericTrap "float to integer overflow" else
  let '(n,d) := fraction src bits in let value := if negative src bits then -(n/d) else n/d in
  if (value <? lower) || (upper <? value) then
    if saturated then Success ((Z.max lower (Z.min upper value)) mod modulus)
    else failure NumericTrap "float to integer overflow"
  else Success (value mod modulus).
Definition fma (width x y z : Z) :=
  let sx := negative width x in let sy := negative width y in let sz := negative width z in
  let ps := xorb sx sy in let ix := is_inf width x in let iy := is_inf width y in let iz := is_inf width z in
  let invalid := (ix && is_zero width y) || (iy && is_zero width x) in
  if is_nan width x || is_nan width y || is_nan width z || invalid || ((ix || iy) && iz && xorb ps sz)
    then binary_nan width x y else
  if ix || iy then signed_bits width ps (infinity width) else if iz then z else
  let '(nx,dx) := fraction width x in let '(ny,dy) := fraction width y in let '(nz,dz) := fraction width z in
  let product := if ps then -(nx*ny*dz) else nx*ny*dz in
  let addend := if sz then -(nz*dx*dy) else nz*dx*dy in let result := product+addend in
  let sign := if result =? 0 then ps && sz else result <? 0 in
  let intermediate := if width =? 32 then 64 else width in
  convert intermediate width (of_ratio intermediate sign (Z.abs result) (dx*dy*dz)).
(* Source fmag constructors are converted arithmetically, without imposing
   canonicality beyond the native final unsigned-word range check. *)
Inductive Magnitude := Norm (m : nat) (e : Z) | Subnorm (m : nat) | Inf | Nan (m : nat).
Definition encode_magnitude (width : Z) (mag : Magnitude) : Z :=
  match mag with
  | Norm m e => (e+bias width) * pow2 (mantissa width) + Z.of_nat m
  | Subnorm m => Z.of_nat m | Inf => infinity width | Nan m => infinity width + Z.of_nat m end.
Definition encode (width : Z) (sign : bool) (mag : Magnitude) : Outcome Z :=
  let bits := signed_bits width sign (encode_magnitude width mag) in checked (valid_word width bits) bits.
Definition decode (width bits : Z) : bool * Magnitude :=
  let frac := bits mod pow2 (mantissa width) in
  let exp := bits / pow2 (mantissa width) mod pow2 (exponent width) in
  let mag := if exp =? 0 then Subnorm (Z.to_nat frac) else
    if exp =? pow2 (exponent width)-1 then if frac =? 0 then Inf else Nan (Z.to_nat frac)
    else Norm (Z.to_nat frac) (exp-bias width) in (negative width bits,mag).
Definition of_bytes (width : Z) (bytes : list nat) : Outcome Z :=
  checked (valid_bytes bytes) (wrap width (decode_bytes bytes)).
Definition checked_binary (width : Z) (op : string) (x y : Z) : Outcome Z :=
  checked (valid_word width x && valid_word width y) (binary width op x y).
Definition checked_compare (width : Z) (op : string) (x y : Z) : Outcome nat :=
  checked (valid_word width x && valid_word width y) (bool_nat (compare width op x y)).
End WasmFloat.
