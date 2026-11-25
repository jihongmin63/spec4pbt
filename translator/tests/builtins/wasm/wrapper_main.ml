open Coq_ir
let () =
 let inputs=Array.to_list Sys.argv |> List.tl in
 let source=match Pass.parse inputs with Ok x->x|Error _->failwith "parse" in
 let raw=match Pass.algo inputs with Ok x->x|Error _->failwith "algo" in
 let spec,_=Context.restore_empty_syntax source raw in
 let ctx=match Context.build ~profile:{name="wasm"} spec with Ok x->x|Error _->failwith "context" in
 let data=match Data.lower ctx with Ok x->x|Error _->failwith "data" in
 let dir=Sys.getenv "WASM_WRAPPER_OUTPUT" in
 let write name text=let c=open_out(Filename.concat dir name)in output_string c text;close_out c in
 write "Types_0000.v" (Emit_data.render ctx data);
 let ds=List.filter(fun(d:Context.declaration)->d.kind="BuiltinDecD" && List.mem_assoc d.source_name Wasm_bindings.signatures)ctx.Context.declarations in
 let defs=List.map(fun(d:Context.declaration)->
  let s=Option.get d.signature in
  let parameters=List.mapi(fun i t->{name="arg"^string_of_int i;typ=Lower_expr.typ ctx t})s.argument_types in
  let body=Wasm_bindings.lower_exn ctx d parameters in
  let action_code=match body.node with
    | Primitive_action(code,[]) -> code
    | _ -> failwith("non-primitive Wasm builtin adapter: "^d.source_name) in
  "Definition B_"^d.source_name^" "^String.concat " " (List.map Render.binding parameters)^" : Action Call "^Emit_data.render_type body.result^" := "^action_code^".\n")ds in
 let c typ name xs=Render.apply (Wasm_bindings.ctor ctx typ name) xs in
 let num tag x=c "op" tag [x] and vec x=c "vecop" "V128" [x] in
 let lane shape op=c "vecop" "V128" [c "laneop" shape [op]] in
 let i32op family op=c "op" "I32" [c family op []] in
 let source_float_zero=c "f32" "POS" [c "fmag" "SUBNORM" ["0%nat"]] in
 let failed_binary="B_eval_binop "^i32op "ibinop" "IAdd"^" "^num "I64" "1%nat"^" "^num "I32" "2%nat" in
 let examples=[
  "wrapper_scalar", "B_i32_add 1 2", "Return 3%nat";
  "wrapper_shift_clamp", "B_lsl_ 1%Z (-1)%Z", "Return 1%Z";
  "wrapper_float_zero", "B_f32_add "^source_float_zero^" "^source_float_zero, "Return "^source_float_zero;
  "wrapper_num_test", "B_eval_testop "^i32op "itestop" "Eqz"^" "^num "I32" "0%nat", "Return 1%nat";
  "wrapper_num_binary", "B_eval_binop "^i32op "ibinop" "IAdd"^" "^num "I32" "1%nat"^" "^num "I32" "2%nat", "Return "^c "numresult" "NumValue" [num "I32" "3%nat"];
  "wrapper_num_trap", "B_eval_binop "^i32op "ibinop" "IDivU"^" "^num "I32" "1%nat"^" "^num "I32" "0%nat", "Return "^c "numresult" "NumTrap" [];
  "wrapper_num_wrong_operand_unmatches", failed_binary, "Unmatched";
  "wrapper_slice_out_of_bounds_unmatches", "B_slice_bytes [1%nat] 1%nat 1%nat", "Unmatched";
  "wrapper_replace_out_of_bounds_unmatches", "B_replace_bytes [] 1%nat []", "Unmatched";
  "wrapper_vec_binary", "B_eval_vbinop "^lane "I8x16" (c "vibinop" "Add" [])^" "^vec "1%nat"^" "^vec "2%nat", "Return "^vec "3%nat";
  "wrapper_vec_shift", "B_eval_vshiftop "^lane "I8x16" (c "vishiftop" "Shl" [])^" "^vec "1%nat"^" "^num "I32" "257%nat", "Return "^vec "2%nat";
  "wrapper_vec_ternary", "B_eval_vternop "^lane "F32x4" (c "vfternop" "RelaxedMadd" [])^" "^vec "0%nat"^" "^vec "0%nat"^" "^vec "0%nat", "Return "^vec "0%nat";
  "wrapper_memory_load", "B_eval_load_num "^Render.apply(Data.record_constructor ctx "memop")[c "numtype" "I32T" [];"0%nat";"0%nat";"None"]^" [1%nat]", "Return "^num "I32" "1%nat";
  "wrapper_memory_store", "B_eval_store_vec "^Render.apply(Data.record_constructor ctx "memop")[c "vectype" "V128T" [];"0%nat";"0%nat";c "void" "VOID" []]^" "^vec "0%nat", "Return (repeat 0%nat 16)";
 ] in
 let proofs=List.map(fun(n,l,r)->"Example "^n^" : ("^l^") = ("^r^"). Proof. vm_compute. reflexivity. Qed.\n")examples in
 let boundary_proofs=
  "Example wrapper_slice_sum_overflow n : Z.of_nat n = 4611686018427387903%Z -> B_slice_bytes [] n 1%nat = Raise {| error_kind := HostInvalidArgument; error_detail := \"Value_array.sub\" |}.\n"^
  "Proof. intro H. unfold B_slice_bytes, WasmScalar.slice_bytes. rewrite H. reflexivity. Qed.\n"^
  "Example wrapper_replace_sum_overflow n : Z.of_nat n = 4611686018427387903%Z -> B_replace_bytes [] n [7%nat] = Raise {| error_kind := HostInvalidArgument; error_detail := \"Value_array.replace_slice\" |}.\n"^
  "Proof. intro H. unfold B_replace_bytes, WasmScalar.replace_bytes. rewrite H. reflexivity. Qed.\n" in
 let bad_profile={ctx with Context.profile={name="p4"}} in
 let d=List.hd ds in
 let rejects thunk = try ignore(thunk());failwith "invalid builtin dispatch accepted" with Wasm_bindings.Unsupported _->() in
 rejects(fun()->Wasm_bindings.validate bad_profile d);
 rejects(fun()->Wasm_bindings.validate ctx {d with kind="FuncDecD"});
 let signature=Option.get d.signature in
 rejects(fun()->Wasm_bindings.validate ctx {d with signature=Some{signature with argument_types=[]}});
 write "WasmWrappers.v" ("From Coq Require Import ZArith List String.\nFrom ALCoq Require Import Execution Values.\nFrom ALCoq.Builtins Require Import WasmScalar WasmFloat WasmVector WasmExecution.\nFrom WasmSpec.Generated Require Import Types_0000.\nImport ListNotations.\nOpen Scope string_scope.\nSet Universe Polymorphism.\nInductive Call : Type -> Type := .\n"^String.concat "\n" defs^String.concat "\n" proofs^boundary_proofs^"\nPrint Assumptions wrapper_num_trap.\nPrint Assumptions wrapper_slice_sum_overflow.\nPrint Assumptions wrapper_replace_sum_overflow.\n");
 write "bindings.json"(Yojson.Safe.pretty_to_string(`List(Wasm_bindings.bindings ctx)));
 Printf.printf "Generated %d Wasm builtin adapters\n%!" (List.length ds)
