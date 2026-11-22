(* Wasm numeric dispatch and memory operations. Apache-2.0 donor provenance
   and license are preserved in translator/tests/builtins/wasm/. *)
From Coq Require Import ZArith List String Bool.
From ALCoq Require Import Execution.
From ALCoq.Builtins Require Import WasmScalar WasmFloat WasmVector.
Import ListNotations WasmScalar.
Set Implicit Arguments.
Set Universe Polymorphism.
Open Scope string_scope.
Open Scope Z_scope.
Module WasmExecution.
(* Normalized tags: integer32, integer64, float32, float64. The generated
   wrappers destruct source constructors and preserve their source types. *)
Inductive NumTag := Int32 | Int64 | Float32 | Float64.
Definition width (tag : NumTag) := match tag with Int32 | Float32 => 32 | Int64 | Float64 => 64 end.
Definition floating (tag : NumTag) := match tag with Float32 | Float64 => true | _ => false end.
Definition tag_equal (a b : NumTag) := match a,b with
  | Int32,Int32 | Int64,Int64 | Float32,Float32 | Float64,Float64 => true | _,_ => false end.
Record Num := { num_tag : NumTag; num_bits : Z }.
Definition valid_num (n : Num) := valid_word (width (num_tag n)) (num_bits n).
Definition checked_num {A} (n : Num) (result : Outcome A) :=
  if valid_num n then result else failure HostConversion "numeric operand out of range".
Inductive NumResult := NumValue (n : Num) | NumTrap.
Definition numeric_result (tag : NumTag) (result : Outcome Z) : Outcome NumResult :=
  match result with
  | Success bits => Success (NumValue {|num_tag := tag; num_bits := bits|})
  | Error e => match error_kind e with NumericTrap => Success NumTrap | _ => Error e end
  | Unmatch => Unmatch end.
Definition eval_testop (tag : NumTag) (n : Num) : Outcome nat := checked_num n
  (if tag_equal tag (num_tag n) && negb (floating tag) then Success (bool_nat (num_bits n =? 0)) else unsupported).
Definition eval_relop (tag : NumTag) (op : string) (a b : Num) : Outcome nat :=
  checked_num a (checked_num b
    (if tag_equal tag (num_tag a) && tag_equal tag (num_tag b) then
      if floating tag then
        if WasmVector.member op ["eq";"ne";"lt";"gt";"le";"ge"]
        then Success (bool_nat (WasmFloat.compare (width tag) op (num_bits a) (num_bits b))) else unsupported
      else map_outcome bool_nat (integer_compare (width tag) op (num_bits a) (num_bits b))
     else unsupported)).
Definition eval_unop (tag : NumTag) (op : string) (packed : Z) (n : Num) : Outcome Num := checked_num n
  (if tag_equal tag (num_tag n) then
    map_outcome (fun x => {|num_tag := tag; num_bits := x|})
      (if floating tag then
        if WasmVector.member op ["abs";"neg";"ceil";"floor";"trunc";"nearest";"sqrt"] then Success (WasmFloat.unary (width tag) op (num_bits n)) else unsupported
       else if WasmVector.member op ["Clz";"Ctz";"Popcnt";"ExtendS"] then integer_unary (width tag) op packed (num_bits n) else unsupported)
   else unsupported).
Definition eval_binop (tag : NumTag) (op : string) (a b : Num) : Outcome NumResult :=
  checked_num a (checked_num b
    (if tag_equal tag (num_tag a) && tag_equal tag (num_tag b) then
      numeric_result tag
        (if floating tag then
          if WasmVector.member op ["add";"sub";"mul";"div";"min";"max";"copysign"]
          then Success (WasmFloat.binary (width tag) op (num_bits a) (num_bits b)) else unsupported
         else if WasmVector.member op ["Add";"Sub";"Mul";"DivS";"DivU";"RemS";"RemU";"And";"Or";"Xor";"Shl";"ShrS";"ShrU";"Rotl";"Rotr"]
         then integer_binary (width tag) op (num_bits a) (num_bits b) else unsupported)
     else unsupported)).
Definition eval_cvtop (dst : NumTag) (op : string) (n : Num) : Outcome NumResult := checked_num n
  (let src := num_tag n in let x := num_bits n in
   let result :=
     if String.eqb op "ExtendSI32" then
       if tag_equal dst Int64 && tag_equal src Int32 then Success (wrap 64 (signed 32 x)) else unsupported else
     if String.eqb op "ExtendUI32" then
       if tag_equal dst Int64 && tag_equal src Int32 then Success x else unsupported else
     if String.eqb op "WrapI64" then
       if tag_equal dst Int32 && tag_equal src Int64 then Success (wrap 32 x) else unsupported else
     if String.eqb op "ReinterpretFloat" then
       if negb (floating dst) && floating src && (width dst =? width src) then Success x else unsupported else
     if String.eqb op "ReinterpretInt" then
       if floating dst && negb (floating src) && (width dst =? width src) then Success x else unsupported else
     if String.eqb op "PromoteF32" then
       if tag_equal dst Float64 && tag_equal src Float32 then Success (WasmFloat.convert 32 64 x) else unsupported else
     if String.eqb op "DemoteF64" then
       if tag_equal dst Float32 && tag_equal src Float64 then Success (WasmFloat.convert 64 32 x) else unsupported else
     if WasmVector.member op ["ConvertSI32";"ConvertUI32";"ConvertSI64";"ConvertUI64"] then
       let sign := WasmVector.member op ["ConvertSI32";"ConvertSI64"] in
       let expected := if WasmVector.member op ["ConvertSI32";"ConvertUI32"] then Int32 else Int64 in
       if floating dst && tag_equal src expected then Success (WasmFloat.of_int (width dst) (if sign then signed (width src) x else x)) else unsupported else
     if WasmVector.member op ["TruncSF32";"TruncUF32";"TruncSF64";"TruncUF64";"TruncSatSF32";"TruncSatUF32";"TruncSatSF64";"TruncSatUF64"] then
       let sign := WasmVector.member op ["TruncSF32";"TruncSF64";"TruncSatSF32";"TruncSatSF64"] in
       let saturated := WasmVector.member op ["TruncSatSF32";"TruncSatUF32";"TruncSatSF64";"TruncSatUF64"] in
       let expected := if WasmVector.member op ["TruncSF32";"TruncUF32";"TruncSatSF32";"TruncSatUF32"] then Float32 else Float64 in
       if negb (floating dst) && tag_equal src expected then WasmFloat.to_int (width src) (width dst) sign saturated x else unsupported
     else unsupported in numeric_result dst result).
Definition mem_valid (align offset : nat) := valid_word 32 (Z.of_nat align) && valid_word 64 (Z.of_nat offset).
Definition check_mem {A} (align offset : nat) (result : Outcome A) :=
  if mem_valid align offset then result else failure HostConversion "memory operand metadata out of range".
Definition pack_width (w : Z) := (w =? 8) || (w =? 16) || (w =? 32) || (w =? 64).
Definition loadop_size (tag : NumTag) (packed : option Z) (align offset : nat) : Outcome nat :=
  check_mem align offset (let w := match packed with None => width tag | Some w => w end in
    if pack_width w then Success (Z.to_nat (w/8)) else unsupported).
Definition storeop_size := loadop_size.
Definition vloadop_size (packed : option Z) (align offset : nat) : Outcome nat :=
  check_mem align offset (match packed with None => Success 16%nat | Some w => if pack_width w then Success (Z.to_nat (w/8)) else unsupported end).
Definition vstoreop_size (align offset : nat) : Outcome nat := check_mem align offset (Success 16%nat).
Definition vlaneop_size (w : Z) (align offset : nat) : Outcome nat :=
  check_mem align offset (if pack_width w then Success (Z.to_nat (w/8)) else unsupported).
Definition eval_load_num (tag : NumTag) (packed : option (Z*bool)) (align offset : nat) (bytes : list nat) : Outcome Num :=
  check_mem align offset
    (if valid_bytes bytes then
      let raw := wrap 64 (decode_bytes bytes) in
      map_outcome (fun bits => {|num_tag := tag; num_bits := bits|})
        (match packed with
         | None => Success (wrap (width tag) raw)
         | Some (w,sign) => if pack_width w && (w <=? width tag) && negb (floating tag) then
             Success (wrap (width tag) (if sign then signed w raw else raw)) else unsupported end)
     else failure HostConversion "invalid memory byte").
(* Native store ignores the descriptor's TYPE after converting its metadata;
   packing is checked against the actual number's width and type. *)
Definition eval_store_num (packed : option Z) (align offset : nat) (n : Num) : Outcome (list nat) :=
  check_mem align offset (checked_num n
    (match packed with
     | None => Success (encode_bytes (Z.to_nat (width (num_tag n)/8)) (num_bits n))
     | Some w => if pack_width w && (w <=? width (num_tag n)) && negb (floating (num_tag n))
         then Success (encode_bytes (Z.to_nat (w/8)) (num_bits n)) else unsupported end)).
Inductive VecExtension := ExtZero | ExtSplat | ExtLane (shape_width : Z) (sign : bool).
Definition eval_load_vec (packed : option (Z*VecExtension)) (align offset : nat) (bytes : list nat) : Outcome Z :=
  check_mem align offset (if valid_bytes bytes then
    let raw := decode_bytes bytes in
    match packed with
    | None => if Nat.leb 16 (List.length bytes) then Success (wrap 128 raw) else failure ExternalAbort "short v128 memory input"
    | Some (w,ext) => if pack_width w then
      let x := wrap 64 raw in
      match ext with
      | ExtZero => if (w =? 32) || (w =? 64) then Success x else unsupported
      | ExtSplat => Success (WasmVector.pack w (repeat x (Z.to_nat (128/w))))
      | ExtLane sw sign => if (w =? 64) && ((sw =? 8) || (sw =? 16) || (sw =? 32)) then
          Success (WasmVector.pack (sw*2) (map (fun i => let n := lane sw x i in if sign then wrap (sw*2) (signed sw n) else n)
            (map Z.of_nat (seq 0 (Z.to_nat (64/sw)))))) else unsupported end
      else unsupported end
    else failure HostConversion "invalid memory byte").
Definition eval_store_vec (align offset : nat) (v : Z) : Outcome (list nat) :=
  check_mem align offset (WasmVector.checked_vec [v] (Success (encode_bytes 16 v))).
Definition eval_load_vec_lane (w : Z) (align offset : nat) (i : Z) (bytes : list nat) (v : Z) : Outcome Z :=
  check_mem align offset (WasmVector.checked_vec [v]
    (if WasmVector.machine_index i then
      if pack_width w && valid_bytes bytes then
        let raw := wrap 64 (decode_bytes bytes) in
        Success (if (0 <=? i) && (i <? 128/w) then WasmVector.replace_lane w v i raw else v)
      else failure HostConversion "invalid lane memory input"
     else failure HostConversion "lane index machine integer overflow")).
Definition eval_store_vec_lane (w : Z) (align offset : nat) (i v : Z) : Outcome (list nat) :=
  check_mem align offset (WasmVector.checked_vec [v]
    (if WasmVector.machine_index i then
      if pack_width w && (0 <=? i) && (i <? 128/w)
      then Success (encode_bytes (Z.to_nat (w/8)) (lane w v i))
      else failure ExternalAbort "lane memory extraction out of bounds"
     else failure HostConversion "lane index machine integer overflow")).
End WasmExecution.
