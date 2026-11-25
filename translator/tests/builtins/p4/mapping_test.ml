open Coq_ir
let get = function Ok x -> x | Error ds -> failwith (String.concat "\n" (List.map (fun d -> d.reason) ds))
let rec render_builtin_action action = match action.node with
  | Primitive_action(name,args) -> Render.apply name (List.map Render.expression args)
  | Return value -> Render.apply "(@Return Call _)" [Render.expression value]
  | Bind (name,left,right) -> Render.apply "Bind"
      [render_builtin_action left;
       Render.par ("fun " ^ Render.binding name ^ " => " ^ render_builtin_action right)]
  | _ -> failwith "unexpected P4 builtin adapter action"
let () =
  let spec = match Pass.algo [Sys.argv.(1)] with Ok spec -> spec | Error d -> failwith d.Diagnostic.message in
  let ctx = Context.build ~profile:{name="p4"} spec |> get in
  let builtins = List.filter (fun (d:Context.declaration) -> d.kind="BuiltinDecD") ctx.declarations in
  assert (List.length builtins=47);
  let types=get(Data.lower ctx) in
  let out=Sys.argv.(2) in
  let write name body=let channel=open_out(Filename.concat out name) in output_string channel body;close_out channel in
  write "Types_0000.v" (Emit_data.render ctx types);
  let coq=Buffer.create 10000 in
  Buffer.add_string coq "From Coq Require Import List String ZArith.\nFrom ALCoq Require Import Execution Values Types_0000.\nFrom ALCoq.Builtins Require Import Common P4.\nImport ListNotations.\nSet Universe Polymorphism.\nSection Mapping.\nVariable Call : Type -> Type.\n";
  let parameters d = let signature=Option.get d.Context.signature in
    List.mapi (fun i t -> {name="#arg"^string_of_int i;typ=Lower_expr.typ ctx t}) signature.argument_types in
  List.iter (fun d ->
    let action=Builtins.lower ctx d (parameters d) |> get in
    let rendered=render_builtin_action action in
    assert (String.length rendered>0);
    let signature=Option.get d.Context.signature in
    let type_parameters=List.map(fun p->Data.parameter_name ctx p.Util.Source.it)signature.type_parameters in
    Buffer.add_string coq ("Definition mapped_" ^ d.Context.source_name ^ " " ^ Emit_data.params type_parameters ^ " " ^ Emit_data.capabilities type_parameters ^ " " ^
      String.concat " " (List.map Render.binding (parameters d)) ^ " : Action Call " ^ Emit_data.render_type action.result ^ " := " ^ rendered ^ ".\n");
    Printf.printf "PASS %s\n%!" d.Context.source_name) builtins;
  let first=List.hd builtins in
  let rejected (result:(action,diagnostic list) result) = match result with Error ds -> assert (ds<>[]) | Ok _ -> failwith "expected builtin mapping diagnostic" in
  rejected (Builtins.lower ctx {first with kind="FuncDecD"} (parameters first));
  rejected (Builtins.lower {ctx with profile={name="wasm"}} first (parameters first));
  rejected (Builtins.lower ctx {first with source_name="unsupported_native"} (parameters first));
  let signature=Option.get first.signature in
  let bad={first with signature=Some {signature with argument_types=[]}} in
  rejected (Builtins.lower ctx bad (parameters first));
  let bad={first with signature=Some {signature with output_types=[]}} in
  rejected (Builtins.lower ctx bad (parameters first));
  rejected (Builtins.lower ctx first []);
  let bad={first with signature=Some {signature with argument_types=[Util.Source.($) Lang.Il.TextT first.location]}} in
  rejected (Builtins.lower ctx bad (parameters first));
  let polymorphic=List.find(fun(d:Context.declaration)->d.source_name="rev_")builtins in
  let poly_signature=Option.get polymorphic.signature in
  rejected (Builtins.lower ctx {polymorphic with signature=Some{poly_signature with type_parameters=[]}} (parameters polymorphic));
  let bad={first with signature=Some {signature with output_types=[Util.Source.($) Lang.Il.TextT first.location]}} in
  rejected (Builtins.lower ctx bad (parameters first));
  (match Builtins.bindings ctx with `List mappings -> assert (List.length mappings=47) | _ -> failwith "bindings must be JSON list");
  let wasm=Context.build ~profile:{name="wasm"} spec |> get in
  List.iter(fun name->let d=Option.get(Context.find wasm ~namespace:"dec" name) in
    let signature=Option.get d.Context.signature in
    let arguments=List.mapi(fun i t->{name="#arg"^string_of_int i;typ=Lower_expr.typ wasm t})signature.argument_types in
    ignore(get(Builtins.lower wasm d arguments))) ["union_set";"diff_set"];
  (match Builtins.bindings wasm with `List mappings -> assert(List.length mappings=2) | _->failwith "shared wasm mappings must be JSON list");
  Buffer.add_string coq "End Mapping.\n";
  write "BuiltinMapping.v" (Buffer.contents coq);
  Printf.printf "Mapping checks: 47 P4 and 2 shared Wasm positive; 9 negative cases passed\n%!"
