(** Profile-, declaration-kind-, and signature-checked Wasm builtin adapters.
    Source datatypes stay intact. Every conversion to the pure numeric helpers
    is explicit, and every source constructor is covered by a generated match. *)
open Util.Source
open Lang
open Coq_ir
module E = Lower_expr
exception Unsupported of diagnostic
let fail (d:Context.declaration) reason = raise (Unsupported {stage="builtin-wasm";location=d.location;construct=d.kind;reason})
let par s = "(" ^ s ^ ")"
let app f xs = if xs=[] then f else par (String.concat " " (f::List.map par xs))
let quote = Emit_data.quote
let nat_z x = app "Z.of_nat" [x]
let map f x = app "WasmScalar.map_outcome" [f;x]
let bind x f = app "WasmScalar.bind_outcome" [x;par("fun " ^ fst f ^ " => " ^ snd f)]
let success x = app "Success" [x]
let unsupported = "WasmScalar.unsupported"
let rec keywords = function
  | Domain.Mixfix.Arg _ -> []
  | Domain.Mixfix.Atom a -> (match a.it with Domain.Atom.Keyword k | Domain.Atom.Tag k -> [k] | _->[])
  | Domain.Mixfix.Brack(_,x,_) -> keywords x
  | Domain.Mixfix.Infix(a,b,c) -> keywords a @ keywords(Domain.Mixfix.Atom b) @ keywords c
  | Domain.Mixfix.Seq xs -> List.concat_map keywords xs
let cases ctx name = match (Data.definition ctx name).it with
  | Al.TypD(_,_,{it=Il.VariantT cs;_},_) -> List.map(fun(t,_,_)->
      let mixop,ts=Domain.Mixfix.split t.it in
      String.concat " " (keywords mixop),Data.constructor_name ctx name mixop,ts)cs
  | _ -> invalid_arg("Wasm builtin adapter requires variant " ^ name)
let ctor ctx name label = match List.find_opt(fun(l,_,_)->l=label)(cases ctx name) with
  | Some(_,c,_)->c | None->invalid_arg("missing source constructor " ^ name ^ "." ^ label)
let matching ctx name value branch =
  "match " ^ value ^ " with " ^ String.concat " " (List.mapi(fun i(label,c,ts)->
    let vs=List.mapi(fun j _->"w" ^ string_of_int i ^ "p" ^ string_of_int j)ts in
    "| " ^ String.concat " " (c::vs) ^ " => " ^ branch label vs)(cases ctx name)) ^ " end"
let one = function [x]->x | _->invalid_arg "expected one source constructor payload"
let typename ctx name = Data.type_name ctx name
let rec locals xs body = match xs with []->body | (name,value)::xs->"let " ^ name ^ " := " ^ value ^ " in " ^ locals xs body
let tag = function "I32"|"I32T"->"WasmExecution.Int32"|"I64"|"I64T"->"WasmExecution.Int64"|"F32"|"F32T"->"WasmExecution.Float32"|"F64"|"F64T"->"WasmExecution.Float64"|s->invalid_arg("invalid numeric tag " ^ s)
let width = function "I8x16"->8 |"I16x8"->16|"I32x4"|"F32x4"->32|"I64x2"|"F64x2"->64|s->invalid_arg("invalid lane shape " ^ s)
let float_shape s = String.starts_with ~prefix:"F" s
let source_tag_for_shape = function "I8x16"|"I16x8"|"I32x4"->"I32"|"I64x2"->"I64"|"F32x4"->"F32"|"F64x2"->"F64"|_->assert false
let normalized_integer s = if String.length s>0 && s.[0]='I' then String.sub s 1 (String.length s-1) else s
let normalized_float s = String.lowercase_ascii (if String.length s>1 && s.[0]='F' && Char.uppercase_ascii s.[1]=s.[1] then String.sub s 1 (String.length s-1) else s)
let opcode ctx typ value normalize = matching ctx typ value (fun label vs ->
  if vs<>[] then invalid_arg("opcode has unexpected payload: " ^ typ ^ "." ^ label);
  quote(normalize label))
let prefix ctx =
  let mag_to=matching ctx "fmag" "v" (fun label xs -> match label,xs with
    |"NORM",[m;e]->app "WasmFloat.Norm" [m;e] |"SUBNORM",[m]->app "WasmFloat.Subnorm" [m]
    |"INF",[]->"WasmFloat.Inf" |"NAN",[m]->app "WasmFloat.Nan"[m]|_->assert false) in
  let mag_from="match v with | WasmFloat.Norm m e => " ^ app(ctor ctx "fmag" "NORM")["m";"e"] ^
    " | WasmFloat.Subnorm m => " ^ app(ctor ctx "fmag" "SUBNORM")["m"] ^
    " | WasmFloat.Inf => " ^ ctor ctx "fmag" "INF" ^ " | WasmFloat.Nan m => " ^ app(ctor ctx "fmag" "NAN")["m"] ^ " end" in
  let to_float w = matching ctx ("f"^string_of_int w) "v" (fun label xs ->
    app "WasmFloat.encode" [string_of_int w;string_of_bool(label="NEG");app "mag_to"[one xs]]) in
  let from_float w = "let '(sign,mag) := WasmFloat.decode " ^ string_of_int w ^ " v in if sign then " ^
    app(ctor ctx ("f"^string_of_int w) "NEG")[app "mag_from"["mag"]] ^ " else " ^
    app(ctor ctx ("f"^string_of_int w) "POS")[app "mag_from"["mag"]] in
  let to_num=matching ctx "op" "v" (fun label xs -> let x=one xs in
    let bits=if label="F32" then app "to32"[x] else if label="F64" then app "to64"[x] else success(nat_z x) in
    map (par("fun bits => {| WasmExecution.num_tag := " ^ tag label ^ "; WasmExecution.num_bits := bits |}")) bits) in
  let from_num="match WasmExecution.num_tag v with " ^ String.concat " " (List.map(fun label->
    "| " ^ tag label ^ " => " ^ app(ctor ctx "op" label)[app (if label="F32" then "from32" else if label="F64" then "from64" else "Z.to_nat")["WasmExecution.num_bits v"]])["I32";"I64";"F32";"F64"]) ^ " end" in
  let from_result="match v with | WasmExecution.NumTrap => " ^ ctor ctx "numresult" "NumTrap" ^
    " | WasmExecution.NumValue n => " ^ app(ctor ctx "numresult" "NumValue")[app "from_num"["n"]] ^ " end" in
  let types=["mag_to","fun (v : "^typename ctx "fmag"^") : WasmFloat.Magnitude => "^mag_to;
    "mag_from","fun (v : WasmFloat.Magnitude) : "^typename ctx "fmag"^" => "^mag_from;
    "to32","fun (v : "^typename ctx "f32"^") : Outcome Z => "^to_float 32;
    "to64","fun (v : "^typename ctx "f64"^") : Outcome Z => "^to_float 64;
    "from32","fun (v : Z) : "^typename ctx "f32"^" => "^from_float 32;
    "from64","fun (v : Z) : "^typename ctx "f64"^" => "^from_float 64;
    "to_num","fun (v : "^typename ctx "num_"^") : Outcome WasmExecution.Num => "^to_num;
    "from_num","fun (v : WasmExecution.Num) : "^typename ctx "num_"^" => "^from_num;
    "from_result","fun (v : WasmExecution.NumResult) : "^typename ctx "numresult"^" => "^from_result;
    "to_vec","fun (v : "^typename ctx "vec_"^") : Z => "^matching ctx "vecop" "v" (fun _ xs->nat_z(one xs));
    "from_vec","fun (v : Z) : "^typename ctx "vec_"^" => "^app(ctor ctx "vecop" "V128")[app "Z.to_nat"["v"]];
    "pack_bits","fun (v : "^typename ctx "packtype"^") : Z => "^matching ctx "packtype" "v" (fun l _->String.sub l 1 (String.length l-1));
    "extension","fun (v : "^typename ctx "extension"^") : bool => "^matching ctx "extension" "v" (fun l _->string_of_bool(l="SX"));
    "numtype","fun (v : "^typename ctx "numtype"^") : WasmExecution.NumTag => "^matching ctx "numtype" "v" (fun l _->tag l);
    "vextension","fun (v : "^typename ctx "vextension"^") : WasmExecution.VecExtension => "^matching ctx "vextension" "v" (fun l xs->match l,xs with
      |"ExtZero",[]->"WasmExecution.ExtZero"|"ExtSplat",[]->"WasmExecution.ExtSplat"
      |"ExtLane",[shape;sign]->app "WasmExecution.ExtLane" [par(matching ctx "packshape" shape (fun l _->match l with "Pack8x8"->"8"|"Pack16x4"->"16"|"Pack32x2"->"32"|_->assert false));app "extension"[sign]]
      |_->assert false)] in
  List.map(fun(n,s)->
    let closing=String.index s ')' in
    let arrow=String.index_from s (closing+1) '=' in
    let result=String.sub s (closing+4) (arrow-closing-5) in
    let body=String.sub s (arrow+3) (String.length s-arrow-3) in
    n,par(String.sub s 0 (closing+1) ^ " => (" ^ body ^ " : " ^ result ^ ")"))types

let signatures = [
  "lsl_", (["int";"int"], "int");
  "byte_of_i32", (["nat"], "byte");
  "i31_of_i32", (["nat"], "nat");
  "i32_add", (["nat";"nat"], "nat");
  "i32_sub", (["nat";"nat"], "nat");
  "i32_mul", (["nat";"nat"], "nat");
  "i64_add", (["nat";"nat"], "nat");
  "i64_sub", (["nat";"nat"], "nat");
  "i64_mul", (["nat";"nat"], "nat");
  "f32_add", (["f32";"f32"], "f32");
  "f32_sub", (["f32";"f32"], "f32");
  "f32_mul", (["f32";"f32"], "f32");
  "f64_add", (["f64";"f64"], "f64");
  "f64_sub", (["f64";"f64"], "f64");
  "f64_mul", (["f64";"f64"], "f64");
  "i32_eqz", (["nat"], "nat");
  "i64_eqz", (["nat"], "nat");
  "i32_gt_u", (["nat";"nat"], "nat");
  "i32_le_s", (["nat";"nat"], "nat");
  "i32_le_u", (["nat";"nat"], "nat");
  "i64_le_u", (["nat";"nat"], "nat");
  "i32_ne", (["nat";"nat"], "nat");
  "i32_wrap_i64", (["nat"], "nat");
  "f32_eq", (["f32";"f32"], "nat");
  "f32_ne", (["f32";"f32"], "nat");
  "f32_le", (["f32";"f32"], "nat");
  "f64_eq", (["f64";"f64"], "nat");
  "f64_ne", (["f64";"f64"], "nat");
  "f64_le", (["f64";"f64"], "nat");
  "i32_extend_i8_s", (["nat"], "nat");
  "i32_extend_i16_s", (["nat"], "nat");
  "i31_get_s", (["nat"], "nat");
  "bytes_of_i32", (["nat"], "byte*");
  "i32_of_bytes", (["byte*"], "nat");
  "i64_of_bytes", (["byte*"], "nat");
  "f32_of_bytes", (["byte*"], "f32");
  "f64_of_bytes", (["byte*"], "f64");
  "v128_of_bytes", (["byte*"], "v128");
  "zero_bytes", (["nat"], "byte*");
  "repeat_byte", (["byte";"nat"], "byte*");
  "slice_bytes", (["byte*";"nat";"nat"], "byte*");
  "replace_bytes", (["byte*";"nat";"byte*"], "byte*");
  "eval_testop", (["testop_";"num_"], "nat");
  "eval_relop", (["relop_";"num_";"num_"], "nat");
  "eval_unop", (["unop_";"num_"], "num_");
  "eval_binop", (["binop_";"num_";"num_"], "numresult");
  "eval_cvtop", (["cvtop_";"num_"], "numresult");
  "eval_vtestop", (["vtestop_";"vec_"], "nat");
  "eval_vrelop", (["vrelop_";"vec_";"vec_"], "vec_");
  "eval_vunop", (["vunop_";"vec_"], "vec_");
  "eval_vbinop", (["vbinop_";"vec_";"vec_"], "vec_");
  "eval_vternop", (["vternop_";"vec_";"vec_";"vec_"], "vec_");
  "eval_vcvtop", (["vcvtop_";"vec_"], "vec_");
  "eval_vshiftop", (["vshiftop_";"vec_";"num_"], "vec_");
  "eval_vbitmaskop", (["vbitmaskop_";"vec_"], "num_");
  "eval_vvtestop", (["vvtestop_";"vec_"], "nat");
  "eval_vvunop", (["vvunop_";"vec_"], "vec_");
  "eval_vvbinop", (["vvbinop_";"vec_";"vec_"], "vec_");
  "eval_vvternop", (["vvternop_";"vec_";"vec_";"vec_"], "vec_");
  "eval_vsplatop", (["vsplatop_";"num_"], "vec_");
  "eval_vextractop", (["vextractop_";"vec_"], "num_");
  "eval_vreplaceop", (["vreplaceop_";"vec_";"num_"], "vec_");
  "loadop_size", (["loadop_"], "nat");
  "storeop_size", (["storeop_"], "nat");
  "eval_load_num", (["loadop_";"byte*"], "num_");
  "eval_store_num", (["storeop_";"num_"], "byte*");
  "vloadop_size", (["vloadop_"], "nat");
  "vstoreop_size", (["vstoreop_"], "nat");
  "vlaneop_size", (["vlaneop_"], "nat");
  "eval_load_vec", (["vloadop_";"byte*"], "vec_");
  "eval_store_vec", (["vstoreop_";"vec_"], "byte*");
  "eval_load_vec_lane", (["vlaneop_";"int";"byte*";"vec_"], "vec_");
  "eval_store_vec_lane", (["vlaneop_";"int";"vec_"], "byte*");
  "bytes_of_text", (["text"], "byte*");
]
let validate ctx (d:Context.declaration) =
  if ctx.Context.profile.name<>"wasm" || d.kind<>"BuiltinDecD" then fail d "Wasm builtin dispatch requires the wasm profile and BuiltinDecD";
  let expected=match List.assoc_opt d.source_name signatures with Some x->x |None->fail d ("unsupported Wasm builtin " ^ d.source_name) in
  let s=match d.signature with Some x->x|None->fail d "builtin has no typed signature" in
  let actual=List.map Al.Print.string_of_typ s.argument_types,List.map Al.Print.string_of_typ s.output_types in
  let args,out=expected in
  if s.type_parameters<>[] || actual<>(args,[out]) then fail d "builtin signature differs from pinned Wasm declaration";
  s
let plain = ["byte_of_i32";"i31_of_i32";"i32_add";"i32_sub";"i32_mul";"i64_add";"i64_sub";"i64_mul";
  "i32_eqz";"i64_eqz";"i32_gt_u";"i32_le_s";"i32_le_u";"i64_le_u";"i32_ne";"i32_wrap_i64";
  "i32_extend_i8_s";"i32_extend_i16_s";"i31_get_s";"bytes_of_i32";"i32_of_bytes";"i64_of_bytes";"bytes_of_text";"lsl_"]
let partial = ["v128_of_bytes";"zero_bytes";"repeat_byte";"slice_bytes";"replace_bytes"]
let op_type family floating = (if floating then "f" else "i") ^ (match family with
  |"eval_testop"->"testop"|"eval_relop"->"relop"|"eval_unop"->"unop"|"eval_binop"->"binop"|"eval_cvtop"->"cvtop"|_->assert false)
let numeric ctx name args =
  let op=List.hd args and nums=List.tl args in
  let body = matching ctx "op" op (fun label xs -> let op=one xs in let is_float=String.starts_with ~prefix:"F" label in
    let tag=tag label in let family=op_type name is_float in
    let dispatch op pack = app("WasmExecution."^name) (tag::(if name="eval_testop" then [] else [op]) @
      (if name="eval_unop" then [pack] else []) @ List.mapi(fun i _->"n"^string_of_int i)nums) in
    if name="eval_testop" && is_float then "match "^op^" with end" else
    if name="eval_unop" && not is_float then matching ctx family op (fun label xs->
      dispatch (quote label) (if label="ExtendS" then app "pack_bits"[one xs] else "0%Z")) else
    dispatch (par(opcode ctx family op (if is_float && name<>"eval_cvtop" then normalized_float else if name="eval_binop" then normalized_integer else Fun.id))) "0%Z") in
  let rec numbers i=function []->body | x::rest->bind(app "to_num"[x])("n"^string_of_int i,numbers(i+1)rest) in
  let result=numbers 0 nums in
  if name="eval_unop" then map "from_num" result else if name="eval_binop" || name="eval_cvtop" then map "from_result" result else result
let laneop_type name floating =
  if List.mem name ["eval_vtestop";"eval_vbitmaskop";"eval_vshiftop"] && floating then "void" else
  let family=match name with
    |"eval_vtestop"->"testop"|"eval_vunop"->"unop"|"eval_vrelop"->"relop"|"eval_vbinop"->"binop"
    |"eval_vternop"->"ternop"|"eval_vcvtop"->"cvtop"|"eval_vshiftop"->"shiftop"|"eval_vbitmaskop"->"bitmaskop"
    |"eval_vsplatop"->"splatop"|"eval_vextractop"->"extractop"|"eval_vreplaceop"->"replaceop"|_->assert false in
  if List.mem name ["eval_vsplatop";"eval_vextractop";"eval_vreplaceop"] then "vn"^family else "v"^(if floating then "f" else "i")^family
let rec vector ctx name args =
  let op=List.hd args in let rest=List.tl args in
  let vv=String.starts_with ~prefix:"eval_vv" name in
  let from_vec x=map "from_vec" x in
  let vec x=app "to_vec"[x] in
  if vv then
    let raw=app("WasmVector."^name) ((if name="eval_vvbinop" then [par(matching ctx "vecop" op(fun _ xs->par(opcode ctx "vvbinop" (one xs) Fun.id)))] else []) @ List.map vec rest) in
    if name="eval_vvtestop" then raw else from_vec raw
  else
  let body=matching ctx "vecop" op (fun _ xs->matching ctx "laneop" (one xs) (fun shape xs->
    let op=one xs in let w=string_of_int(width shape)^"%Z" and floating=float_shape shape in
    let fp=string_of_bool floating and source_tag=source_tag_for_shape shape in
    let family=laneop_type name floating in
    if List.mem name ["eval_vtestop";"eval_vshiftop";"eval_vbitmaskop"] && floating then unsupported else
    let dispatch op extra inputs = app("WasmVector."^name)
      ([w] @ (if List.mem name ["eval_vunop";"eval_vrelop";"eval_vbinop";"eval_vternop";"eval_vcvtop"] then [fp] else []) @
       (if List.mem name ["eval_vtestop";"eval_vbitmaskop"] then [] else [op]) @ extra @ inputs) in
    match name,rest with
    | "eval_vsplatop",[n] ->
        bind(app "to_num"[n])("n",if_true_num source_tag "n" (app "WasmVector.eval_vsplatop"[w;app "WasmExecution.width"[tag source_tag];"WasmExecution.num_bits n"]))
    | "eval_vextractop",[v] ->
        matching ctx "vnextractop" op (fun _ xs->let tuple=one xs in
          "let '(idx,ext) := "^tuple^" in " ^
          map (par("fun bits => from_num {| WasmExecution.num_tag := "^tag source_tag^"; WasmExecution.num_bits := bits |}"))
            (app "WasmVector.eval_vextractop"[w;(if width shape<32 then app "extension"["ext"] else "false");vec v;nat_z "idx"]))
    | "eval_vreplaceop",[v;n] ->
        matching ctx "vnreplaceop" op (fun _ xs->bind(app "to_num"[n])("n",if_true_num source_tag "n"
          (app "WasmVector.eval_vreplaceop" [w;app "WasmExecution.width"[tag source_tag];vec v;nat_z(one xs);"WasmExecution.num_bits n"])))
    | "eval_vshiftop",[v;n] -> bind(app "to_num"[n])("n",if_true_num "I32" "n" (dispatch (par(opcode ctx family op Fun.id)) [] [vec v;"WasmExecution.num_bits n"]))
    | "eval_vbinop",[a;b] -> matching ctx family op (fun label xs->
        dispatch(quote(if floating then String.lowercase_ascii label else label)) [if label="Shuffle" then one xs else "[]"] [vec a;vec b])
    | _ -> dispatch (par(opcode ctx family op (if floating && List.mem name ["eval_vunop";"eval_vrelop"] then String.lowercase_ascii else Fun.id))) [] (List.map vec rest))) in
  if name="eval_vtestop" || name="eval_vextractop" then body else
  if name="eval_vbitmaskop" then map (par("fun bits => from_num {| WasmExecution.num_tag := WasmExecution.Int32; WasmExecution.num_bits := bits |}")) body else from_vec body
and if_true_num source n result = "if WasmExecution.tag_equal (WasmExecution.num_tag "^n^") "^tag source^" then "^result^" else WasmScalar.unsupported"
let memory ctx name (s:Context.signature) args =
  let descriptor=List.hd args in let rest=List.tl args in
  let t=Data.unfold_alias ctx (List.hd s.argument_types) in
  let ts=match t.it with Il.VarT(id,ts) when id.it="memop"->ts |_->invalid_arg "memory builtin must take memop" in
  let field label =
    let atom,_=List.find(fun(a,_)->Domain.Atom.string_of_atom a.it=label)(Data.fields ctx "memop") in
    app(Data.field_name ctx "memop" atom) (List.map(fun t->Emit_data.render_type(E.typ ctx t))ts@[descriptor]) in
  let align=field "ALIGN" and offset=field "OFFSET" and packed=field "PACK" in
  let tag=app "numtype"[field "TYPE"] in
  let opack="match "^packed^" with None => None | Some p => Some (pack_bits p) end" in
  let loadpack="match "^packed^" with None => None | Some (p,e) => Some (pack_bits p, extension e) end" in
  let vloadpack="match "^packed^" with None => None | Some (p,e) => Some (pack_bits p, vextension e) end" in
  let pack=app "pack_bits"[packed] in
  let native=app("WasmExecution."^name) in
  let vec v=app "to_vec"[v] in
  match name,rest with
  | "loadop_size",[] -> native[tag;par("match "^packed^" with None => None | Some (p,_) => Some (pack_bits p) end");align;offset]
  | "storeop_size",[] -> native[tag;par opack;align;offset]
  | "vloadop_size",[] -> native[par("match "^packed^" with None => None | Some (p,_) => Some (pack_bits p) end");align;offset]
  | "vstoreop_size",[] -> native[align;offset]
  | "vlaneop_size",[] -> native[pack;align;offset]
  | "eval_load_num",[bytes] -> map "from_num" (native[tag;par loadpack;align;offset;bytes])
  | "eval_store_num",[n] -> bind(app "to_num"[n])("n",native[par opack;align;offset;"n"])
  | "eval_load_vec",[bytes] -> map "from_vec" (native[par vloadpack;align;offset;bytes])
  | "eval_store_vec",[v] -> native[align;offset;vec v]
  | "eval_load_vec_lane",[i;bytes;v] -> map "from_vec" (native[pack;align;offset;i;bytes;vec v])
  | "eval_store_vec_lane",[i;v] -> native[pack;align;offset;i;vec v]
  | _->invalid_arg("unexpected memory builtin arguments: " ^ name)
let lower_exn ctx (d:Context.declaration) (parameters:binding list) : action =
  let s=validate ctx d in
  if List.length parameters<>List.length s.argument_types then fail d "builtin parameter arity mismatch";
  List.iter2(fun (p:binding) t->if p.typ<>E.typ ctx t then fail d "builtin parameter type mismatch")parameters s.argument_types;
  let name=d.source_name and args=List.map(fun(p:binding)->Render.identifier p.name)parameters in
  let result=E.typ ctx (List.hd s.output_types) in
  let computation=if List.mem name plain then success(app("WasmScalar."^name)args) else
    if List.mem name partial then app("WasmScalar."^name)args else
    if String.starts_with ~prefix:"f32_" name || String.starts_with ~prefix:"f64_" name then
      let w=String.sub name 1 2 in let op=String.sub name 4 (String.length name-4) in
      (match args with
       | [bytes] when op="of_bytes" -> map ("from"^w) (app "WasmFloat.of_bytes"[w;bytes])
       | [a;b] -> bind(app("to"^w)[a])("a",bind(app("to"^w)[b])("b",
           if List.mem op ["eq";"ne";"le"] then success(app "WasmScalar.bool_nat"[app "WasmFloat.compare"[w;quote op;"a";"b"]])
           else success(app("from"^w)[app "WasmFloat.binary"[w;quote op;"a";"b"]])))
       | _->fail d "unexpected floating-point signature") else
    if List.mem name ["eval_testop";"eval_relop";"eval_unop";"eval_binop";"eval_cvtop"] then numeric ctx name args else
    if String.starts_with ~prefix:"eval_v" name && not(List.mem name ["eval_load_vec";"eval_store_vec";"eval_load_vec_lane";"eval_store_vec_lane"]) then vector ctx name args else
    memory ctx name s args in
  let needs_prefix=not(List.mem name plain || List.mem name partial) in
  let code=app "WasmScalar.lift"[par(if needs_prefix then locals(prefix ctx)computation else computation)] in
  {result;node=Primitive_action(code,[])}
let bindings ctx =
  List.filter_map(fun(d:Context.declaration)->if d.kind="BuiltinDecD" && List.mem_assoc d.source_name signatures then
    let _=validate ctx d in Some (`Assoc ["source_name",`String d.source_name;"kind",`String d.kind;
      "signature",Context.signature_to_json(Option.get d.signature);
      "adapter",`String "Wasm_bindings.lower_exn";
      "implementation",`String (if List.mem d.source_name plain || List.mem d.source_name partial then "WasmScalar."^d.source_name
        else if String.starts_with ~prefix:"f" d.source_name then "WasmFloat" else if String.starts_with ~prefix:"eval_v" d.source_name then "WasmVector" else "WasmExecution");
      "failure_policy",`String "native host conversion and abort distinguished; numeric traps become typed NumTrap; no extern fallback"]) else None)ctx.Context.declarations
