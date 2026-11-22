open Coq_ir
include Render

let namespace ctx =
  match ctx.Context.profile.name with "p4"->"P4Spec"|"wasm"->"WasmSpec"|_->"FixtureSpec"
let type_parameters ctx (signature:Context.signature) = List.map(fun p->Data.parameter_name ctx p.Util.Source.it)signature.type_parameters
let param_binders ps = String.concat " " (List.map(fun p->par(p^" : Set"))ps @ List.map(fun p->par("ops_"^p^" : ValueOps@{Set} "^p))ps)
let parameter_values ps = ps @ List.map(fun p->"ops_"^p)ps
let result_type ctx (signature:Context.signature) =
  match List.map(Lower_expr.typ ctx)signature.output_types with []->Unit|[t]->t|ts->Product ts
let signature_inputs ctx (signature:Context.signature) = List.map(fun p->Lower_expr.typ ctx(List.nth signature.argument_types p))signature.input_positions
let declarations ctx = List.filter(fun(d:Context.declaration)->Option.is_some d.signature)ctx.Context.declarations
let references ctx =
  let json=Context.to_json ctx in
  let names=match json with `Assoc fields -> (match List.assoc_opt "function_references" fields with
      | Some(`List refs)->List.filter_map(function `Assoc fields ->
          (match List.assoc_opt "global_declaration" fields,List.assoc_opt "reference" fields with Some(`String _),Some(`String name)->Some name|_->None)|_->None)refs
      | _->[])|_->[] in
  List.filter(fun(d:Context.declaration)->d.namespace="dec" && List.mem d.source_name names)ctx.Context.declarations
let header ctx imports =
  "From Coq Require Import String Ascii List Bool ZArith Arith.\nFrom ALCoq Require Import Execution Values.\n" ^
  (if imports=[] then "" else "From " ^ namespace ctx ^ ".Generated Require Import " ^ String.concat " " imports ^ ".\n") ^
  "Import ListNotations.\nOpen Scope string_scope.\nSet Universe Polymorphism.\nUnset Implicit Arguments.\n"
let render_references ctx =
  let b=Buffer.create 10000 in let line s=Buffer.add_string b(s^"\n") in
  line(header ctx ["Types_0000"]);
  line "Unset Universe Polymorphism.";line "Unset Elimination Schemes.";
  line "Inductive FunctionRef : Set -> Set -> Set :=";
  List.iter(fun(d:Context.declaration)->let s=Option.get d.signature in let ps=type_parameters ctx s in
    line("| " ^ reference_constructor d.generated_name ^ " : " ^
      (if ps=[]then ""else "forall " ^ param_binders ps ^ ", ") ^
      "FunctionRef " ^ Emit_data.render_type(Product(signature_inputs ctx s)) ^ " " ^ Emit_data.render_type(result_type ctx s))) (references ctx);
  line ".";
  line "Definition function_ref_name {A B} (r : FunctionRef A B) : string :=";
  line "match r with";
  List.iter(fun(d:Context.declaration)->let ps=type_parameters ctx(Option.get d.signature) in
    line("| " ^ String.concat " " (reference_constructor d.generated_name::List.map(fun _->"_")(parameter_values ps)) ^ " => " ^ Emit_data.quote("$"^d.source_name)))(references ctx);
  line "end.";
  line "Definition function_ref_ops {A B} : ValueOps@{Set} (FunctionRef A B) := {| equal_value := fun a b => String.eqb (function_ref_name a) (function_ref_name b); compare_value := fun _ _ => Eq; print_value := fun _ a => function_ref_name a; unparse_value := fun _ => None |}.";
  Buffer.contents b
let render_calls ctx =
  let b=Buffer.create 30000 in let line s=Buffer.add_string b(s^"\n") in
  line(header ctx ["Types_0000";"References"]);line "Unset Universe Polymorphism.";line "Unset Elimination Schemes.";line "Inductive Call : Set -> Type@{Set+1} :=";
  List.iter(fun(d:Context.declaration)->let s=Option.get d.signature in let ps=type_parameters ctx s in
    let arrow=List.map Emit_data.render_type(signature_inputs ctx s) @ ["Call " ^ Emit_data.render_type(result_type ctx s)] in
    line("| " ^ call_constructor d.generated_name ^ " : " ^ (if ps=[]then""else"forall "^param_binders ps^", ") ^ String.concat " -> " arrow))(declarations ctx);
  line "| ApplyReference : forall A B, FunctionRef A B -> A -> Call B.";
  line "Arguments ApplyReference {A B} _ _.";
  Buffer.contents b
let render_reference_body ctx =
  let b=Buffer.create 20000 in let line s=Buffer.add_string b(s^"\n") in
  line "Definition reference_body {A B} (r : FunctionRef A B) : A -> Action Call B :=";
  line "match r in FunctionRef input_type output_type return input_type -> Action Call output_type with";
  List.iter(fun(d:Context.declaration)->let s=Option.get d.signature in let ps=type_parameters ctx s in
    let args=List.mapi(fun i _->"a"^string_of_int i)(signature_inputs ctx s) in
    line("| " ^ String.concat " " (reference_constructor d.generated_name::parameter_values ps) ^ " => fun input => match input with " ^ tuple args ^ " => Invoke " ^
        apply(call_constructor d.generated_name)(parameter_values ps@args) ^ " end"))(references ctx);
  line "end.";Buffer.contents b
let render_bodies ctx bodies =
  header ctx ["Types_0000";"Casts";"References";"Calls"] ^
  (match ctx.Context.profile.name with
   | "p4" -> "From ALCoq.Builtins Require Import Common P4.\n"
   | "wasm" -> "From ALCoq.Builtins Require Import Common P4 WasmScalar WasmFloat WasmVector WasmExecution.\n"
   | _ -> "") ^ String.concat "\n" (List.map(fun body->
    let d=Context.String_map.find body.call_name ctx.Context.by_generated_name in
    let s=Option.get d.signature in let ps=type_parameters ctx s in
    "Definition B_" ^ body.call_name ^ " " ^ param_binders ps ^ " " ^ String.concat " " (List.map binding body.parameters) ^
    " : Action Call " ^ Emit_data.render_type body.result ^ " :=\n" ^ action body.action ^ ".\n")bodies)
let render_program ctx bodies body_files =
  let b=Buffer.create 40000 in let line s=Buffer.add_string b(s^"\n") in
  line(header ctx (["Types_0000";"References";"Calls"]@body_files));line(render_reference_body ctx);
  line "Definition Body {A} (call : Call A) : Action Call A :=";
  line "match call in Call T return Action Call T with";
  List.iter(fun body -> let d=Context.String_map.find body.call_name ctx.Context.by_generated_name in
    let ps=type_parameters ctx(Option.get d.signature) in let args=List.map(fun(b:binding)->identifier b.name)body.parameters in
    let all=parameter_values ps@args in
    line("| " ^ String.concat " " (call_constructor body.call_name::all) ^ " => " ^ apply("B_"^body.call_name)all))bodies;
  line "| ApplyReference reference input => reference_body reference input";
  line "end.";Buffer.contents b
let render_relations ctx ~inductive =
  header ctx (["Types_0000";"References";"Calls";"Program"] @
    if inductive then ["InductiveRelations"] else []) ^ String.concat "\n"(List.map(fun(d:Context.declaration)->
    let s=Option.get d.signature in let ps=type_parameters ctx s in
    let arguments=List.mapi(fun i typ->{name="#public"^string_of_int i;typ=Lower_expr.typ ctx typ})s.argument_types in
    let outputs=if d.namespace="rel" then List.map(List.nth arguments)s.output_positions else [{name="#result";typ=result_type ctx s}] in
    let inputs=List.map(List.nth arguments)s.input_positions in
    let out=tuple(List.map(fun(b:binding)->identifier b.name)outputs) in
    let args=if d.namespace="rel"then arguments else arguments@outputs in
    let values=parameter_values ps@List.map(fun(b:binding)->identifier b.name)args in
    let public=apply d.generated_name values in
    let execution = if inductive then
      apply (d.generated_name ^ "_execute")
        (parameter_values ps @ List.map(fun(b:binding)->identifier b.name)inputs @
         ["{| next_fresh := 0 |}"; "Success " ^ par out; "final"])
    else "Eval (@Body) (Invoke " ^ apply(call_constructor d.generated_name)
      (parameter_values ps@List.map(fun(b:binding)->identifier b.name)inputs) ^
      ") {| next_fresh := 0 |} (Success " ^ out ^ ") final" in
    let definition="Definition " ^ d.generated_name ^ " " ^ param_binders ps ^ " " ^ String.concat " " (List.map binding args) ^ " : Prop :=\n" ^
      "exists final, " ^ execution ^ ".\n" in
    if d.kind="ExternRelD" || d.kind="ExternDecD" then
      let external_name="External_"^d.generated_name in
      definition ^ "Inductive " ^ external_name ^ " " ^ param_binders ps ^ " " ^ String.concat " " (List.map binding args) ^
      " : Prop :=\n| Permit_" ^ d.generated_name ^ " : " ^ apply external_name values ^ ".\n" ^
      "Lemma " ^ external_name ^ "_realized " ^ param_binders ps ^ " " ^ String.concat " " (List.map binding args) ^
      " : " ^ apply external_name values ^ " -> " ^ public ^ ".\n" ^
      (if inductive then
        "Proof. intros _. unfold " ^ d.generated_name ^ ". eexists. constructor. Qed.\n"
       else "Proof. intros _. unfold " ^ d.generated_name ^ ". eexists. apply eval_invoke. cbn. apply eval_choose. Qed.\n")
    else definition)(declarations ctx))
let rec mkdir path = if not(Sys.file_exists path)then(mkdir(Filename.dirname path);Unix.mkdir path 0o755)
let write_file path text = let file=open_out path in Fun.protect ~finally:(fun()->close_out file)(fun()->output_string file text)
exception Direct_unsupported of Coq_ir.diagnostic list
let write ~out_dir ~inductive ctx ~data ~bodies = try
  let direct = if inductive then match Inductive_emit.render ctx bodies with
    | Ok source -> Some source
    | Error diagnostics -> raise (Direct_unsupported diagnostics)
    else None in
  let generated=Filename.concat out_dir "Generated" in mkdir generated;
  write_file(Filename.concat generated "Types_0000.v")(Emit_data.render ctx data);
  write_file(Filename.concat generated "Casts.v")(header ctx ["Types_0000"] ^ Casts.render ctx data);
  write_file(Filename.concat generated "References.v")(render_references ctx);
  write_file(Filename.concat generated "Calls.v")(render_calls ctx);
  let rec chunks i= function []->[]|bodies->
    let rec take n xs=if n=0 then[],xs else match xs with []->[],[]|x::xs->let a,b=take(n-1)xs in x::a,b in
    let chunk,rest=take 40 bodies in let name=Printf.sprintf "Bodies_%04d" i in
    write_file(Filename.concat generated(name^".v"))(render_bodies ctx chunk);name::chunks(i+1)rest in
  let body_files=chunks 0 bodies in
  write_file(Filename.concat generated "Program.v")(render_program ctx bodies body_files);
  Option.iter (fun source -> write_file(Filename.concat generated "InductiveRelations.v")
    (header ctx ["Types_0000";"Casts";"References";"Calls"] ^ source)) direct;
  write_file(Filename.concat generated "Relations_0000.v")(render_relations ctx ~inductive);
  write_file(Filename.concat out_dir "Spec.v")("From " ^ namespace ctx ^ ".Generated Require Export Types_0000 References Calls Program Relations_0000" ^
    (if inductive then " InductiveRelations" else "") ^ ".\n");
  Ok()
with Data.Unsupported d->Error[d]
   | Direct_unsupported diagnostics -> Error diagnostics
   | exn->Error[{stage="emission";location=Util.Source.no_region;construct="Coq";reason=Printexc.to_string exn}]
