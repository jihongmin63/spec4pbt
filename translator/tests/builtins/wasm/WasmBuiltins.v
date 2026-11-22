From Coq Require Import ZArith List String.
From ALCoq Require Import Execution.
From ALCoq.Builtins Require Import WasmScalar WasmFloat WasmVector WasmExecution.
Import ListNotations WasmScalar.
Set Universe Polymorphism.
Open Scope string_scope.
Open Scope Z_scope.
Definition kind {A} (x : Outcome A) : option ErrorKind :=
  match x with Error e => Some (error_kind e) | _ => None end.
Example scalar_add : i32_add 8 9 = 17%nat. Proof. vm_compute. reflexivity. Qed.
Example arbitrary_natural_byte : i32_of_bytes [256%nat] = 256%nat. Proof. vm_compute. reflexivity. Qed.
Example valid_byte_conversion : byte_of_i32 511 = 255%nat. Proof. vm_compute. reflexivity. Qed.
Example zero_bytes_test : zero_bytes 3 = Success [0%nat;0%nat;0%nat]. Proof. reflexivity. Qed.
Example repeat_noncanonical_byte : repeat_byte 999 2 = Success [999%nat;999%nat]. Proof. reflexivity. Qed.
Example slice_good : slice_bytes [1%nat;2%nat;3%nat] 1 2 = Success [2%nat;3%nat]. Proof. vm_compute. reflexivity. Qed.
Example slice_bad : kind (slice_bytes [1%nat] 1 1) = Some ExternalAbort. Proof. vm_compute. reflexivity. Qed.
Example replace_good : replace_bytes [1%nat;2%nat;3%nat] 1 [9%nat] = Success [1%nat;9%nat;3%nat]. Proof. vm_compute. reflexivity. Qed.
Example replace_bad : kind (replace_bytes [] 1 []) = Some ExternalAbort. Proof. vm_compute. reflexivity. Qed.
Example raw_string_bytes : bytes_of_text (String (Ascii.ascii_of_nat 195) (String (Ascii.ascii_of_nat 169) "")) = [195%nat;169%nat]. Proof. reflexivity. Qed.
Example signed_min : signed 32 2147483648 = -2147483648. Proof. vm_compute. reflexivity. Qed.
Example signed_modulus : signed 32 4294967297 = 1. Proof. vm_compute. reflexivity. Qed.
Example invalid_numeric : kind (integer_binary 32 "Add" 4294967296 0) = Some HostConversion. Proof. vm_compute. reflexivity. Qed.
Example wide_pack_native : integer_unary 32 "ExtendS" 64 2147483649 = Success 2147483649. Proof. vm_compute. reflexivity. Qed.
Example div_zero : kind (integer_binary 32 "DivU" 9 0) = Some NumericTrap. Proof. vm_compute. reflexivity. Qed.
Example div_overflow : kind (integer_binary 32 "DivS" 2147483648 4294967295) = Some NumericTrap. Proof. vm_compute. reflexivity. Qed.
Example rem_overflow_defined : integer_binary 32 "RemS" 2147483648 4294967295 = Success 0. Proof. vm_compute. reflexivity. Qed.
Example div_negative_truncates : integer_binary 32 "DivS" 4294967289 2 = Success 4294967293. Proof. vm_compute. reflexivity. Qed.
Example shift_masks_count : integer_binary 32 "Shl" 1 33 = Success 2. Proof. vm_compute. reflexivity. Qed.
Example float_encode_noncanonical : WasmFloat.encode 32 false (WasmFloat.Norm 0 (-127)) = Success 0. Proof. vm_compute. reflexivity. Qed.
Example float_encode_reject : kind (WasmFloat.encode 32 false (WasmFloat.Norm 0 (-128))) = Some HostConversion. Proof. vm_compute. reflexivity. Qed.
Example float_nan_comparison : WasmFloat.compare 32 "eq" 2143289345 2143289345 = false. Proof. vm_compute. reflexivity. Qed.
Example float_nan_payload : WasmFloat.binary 32 "add" 2139095041 1065353216 = 2143289345. Proof. vm_compute. reflexivity. Qed.
Example float_zero_min : WasmFloat.binary 32 "min" 0 2147483648 = 2147483648. Proof. vm_compute. reflexivity. Qed.
Example float_zero_max : WasmFloat.binary 32 "max" 0 2147483648 = 0. Proof. vm_compute. reflexivity. Qed.
Example float_ties_even : WasmFloat.unary 32 "nearest" 1075838976 = 1073741824. Proof. vm_compute. reflexivity. Qed.
Example float_nan_trap : kind (WasmFloat.to_int 32 32 true false 2143289344) = Some NumericTrap. Proof. vm_compute. reflexivity. Qed.
Example float_nan_sat : WasmFloat.to_int 32 32 true true 2143289344 = Success 0. Proof. vm_compute. reflexivity. Qed.
Example float_invalid_byte : kind (WasmFloat.of_bytes 32 [256%nat]) = Some HostConversion. Proof. vm_compute. reflexivity. Qed.
Example float_short_bytes : WasmFloat.of_bytes 32 [] = Success 0. Proof. vm_compute. reflexivity. Qed.
Example vec_invalid : kind (WasmVector.eval_vvunop (pow2 128)) = Some HostConversion. Proof. vm_compute. reflexivity. Qed.
Example vec_shift_masks : WasmVector.eval_vshiftop 8 "Shl" 1 257 = Success 2. Proof. vm_compute. reflexivity. Qed.
Example vec_replace_outside : WasmVector.eval_vreplaceop 8 32 1 16 8 = Success 1. Proof. vm_compute. reflexivity. Qed.
Example vec_replace_negative : WasmVector.eval_vreplaceop 8 32 1 (-1) 8 = Success 1. Proof. vm_compute. reflexivity. Qed.
Example vec_extract_negative : kind (WasmVector.eval_vextractop 8 false 1 (-1)) = Some ExternalAbort. Proof. vm_compute. reflexivity. Qed.
Example vec_extract_host_overflow : kind (WasmVector.eval_vextractop 8 false 1 (pow2 62)) = Some HostConversion. Proof. vm_compute. reflexivity. Qed.
Example vec_shuffle_bad : kind (WasmVector.eval_vbinop 8 false "Shuffle" [32%nat] 0 0) = Some StructureError. Proof. vm_compute. reflexivity. Qed.
Example vec_popcnt_invalid_shape : kind (WasmVector.eval_vunop 16 false "Popcnt" 0) = Some StructureError. Proof. vm_compute. reflexivity. Qed.
Example vec_relaxed_dot : WasmVector.eval_vbinop 16 false "RelaxedDot" [] 65535 257 = Success 65534. Proof. vm_compute. reflexivity. Qed.
Import WasmExecution.
Definition num (tag : NumTag) (bits : Z) : Num := {|num_tag := tag;num_bits := bits|}.
Example typed_div_trap : eval_binop Int32 "DivS" (num Int32 2147483648) (num Int32 4294967295) = Success NumTrap. Proof. vm_compute. reflexivity. Qed.
Example typed_conversion_trap : eval_cvtop Int32 "TruncSF32" (num Float32 2143289344) = Success NumTrap. Proof. vm_compute. reflexivity. Qed.
Example typed_wrong_operand : kind (eval_binop Int32 "Add" (num Int64 2) (num Int32 1)) = Some StructureError. Proof. vm_compute. reflexivity. Qed.
Example mem_invalid_bytes : kind (eval_load_num Int32 None 0 0 [256%nat]) = Some HostConversion. Proof. vm_compute. reflexivity. Qed.
Example mem_short_num : eval_load_num Int32 None 0 0 [1%nat] = Success (num Int32 1). Proof. vm_compute. reflexivity. Qed.
Example mem_signed_packed : eval_load_num Int32 (Some (8,true)) 0 0 [255%nat] = Success (num Int32 4294967295). Proof. vm_compute. reflexivity. Qed.
Example mem_store_packed : eval_store_num (Some 8) 0 0 (num Int32 511) = Success [255%nat]. Proof. vm_compute. reflexivity. Qed.
Example mem_float_packed : kind (eval_store_num (Some 8) 0 0 (num Float32 0)) = Some StructureError. Proof. vm_compute. reflexivity. Qed.
Example mem_vec_short : kind (eval_load_vec None 0 0 [0%nat]) = Some ExternalAbort. Proof. vm_compute. reflexivity. Qed.
Example mem_vec_splat : eval_load_vec (Some (64,ExtSplat)) 0 0 [1%nat] = Success (1 + pow2 64). Proof. vm_compute. reflexivity. Qed.
Example mem_vec_zero_uses_low64 : eval_load_vec (Some (32,ExtZero)) 0 0 [0%nat;0%nat;0%nat;0%nat;1%nat] = Success (pow2 32). Proof. vm_compute. reflexivity. Qed.
Example mem_lane_negative_load : eval_load_vec_lane 8 0 0 (-1) [9%nat] 1 = Success 1. Proof. vm_compute. reflexivity. Qed.
Example mem_lane_negative_store : kind (eval_store_vec_lane 8 0 0 (-1) 1) = Some ExternalAbort. Proof. vm_compute. reflexivity. Qed.
Example mem_lane_host_overflow : kind (eval_load_vec_lane 8 0 0 (pow2 62) [] 0) = Some HostConversion. Proof. vm_compute. reflexivity. Qed.
Example memory_descriptor_invalid : mem_valid 0 0 = true /\ valid_word 64 (pow2 64) = false. Proof. vm_compute. split;reflexivity. Qed.
Example lsl_negative : lsl_ 3 (-9) = 3. Proof. vm_compute. reflexivity. Qed.
Example lsl_small : lsl_ 3 4 = 48. Proof. vm_compute. reflexivity. Qed.
Example lsl_saturates : lsl_ 3 4097 = Z.shiftl 3 4096. Proof. vm_compute. reflexivity. Qed.
Example whole_vec_and : WasmVector.eval_vvbinop "And" 7 3 = Success 3. Proof. vm_compute. reflexivity. Qed.
Example whole_vec_select : WasmVector.eval_vvternop 7 0 3 = Success 3. Proof. vm_compute. reflexivity. Qed.
Example splat_i64 : WasmVector.eval_vsplatop 64 64 1 = Success (1+pow2 64). Proof. vm_compute. reflexivity. Qed.
Example scalar_test : eval_testop Int32 (num Int32 0) = Success 1%nat. Proof. vm_compute. reflexivity. Qed.
Example scalar_rel : eval_relop Int32 "LtS" (num Int32 4294967295) (num Int32 0) = Success 1%nat. Proof. vm_compute. reflexivity. Qed.
Example scalar_unary : eval_unop Int32 "ExtendS" 8 (num Int32 255) = Success (num Int32 4294967295). Proof. vm_compute. reflexivity. Qed.
Example mem_size : loadop_size Int32 None 0 0 = Success 4%nat. Proof. vm_compute. reflexivity. Qed.
Example mem_store_size : storeop_size Int64 (Some 8) 0 0 = Success 1%nat. Proof. vm_compute. reflexivity. Qed.
Example mem_vec_size : vloadop_size None 0 0 = Success 16%nat. Proof. vm_compute. reflexivity. Qed.
Example mem_vec_store_size : vstoreop_size 0 0 = Success 16%nat. Proof. vm_compute. reflexivity. Qed.
Example mem_lane_size : vlaneop_size 16 0 0 = Success 2%nat. Proof. vm_compute. reflexivity. Qed.
Example mem_store_vector : eval_store_vec 0 0 0 = Success (repeat 0%nat 16). Proof. vm_compute. reflexivity. Qed.
Example mem_load_vector : eval_load_vec None 0 0 (1%nat::repeat 0%nat 15) = Success 1. Proof. vm_compute. reflexivity. Qed.
Example mem_lane_valid : eval_load_vec_lane 8 0 0 0 [9%nat] 0 = Success 9. Proof. vm_compute. reflexivity. Qed.
Example mem_lane_store_valid : eval_store_vec_lane 8 0 0 1 258 = Success [1%nat]. Proof. vm_compute. reflexivity. Qed.
Inductive NoCall : Type -> Type := .
Definition no_body A (c : NoCall A) : Action NoCall A := match c with end.
Example lifted_error_stops_alternative :
 Eval no_body (OrElse (lift (failure HostConversion "bad" : Outcome Z)) (Return 7)) {| next_fresh := 0 |}
   (failure HostConversion "bad") {| next_fresh := 0 |}.
Proof. apply eval_or_error. constructor. Qed.
Print Assumptions lifted_error_stops_alternative.
Print Assumptions typed_conversion_trap.
Print Assumptions float_ties_even.
