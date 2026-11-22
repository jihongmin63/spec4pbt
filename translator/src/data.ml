open Util.Source
open Lang
open Coq_ir
module M = Map.Make(String)
module S = Set.Make(String)

exception Unsupported of diagnostic
let () = Printexc.register_printer (function Unsupported d -> Some (d.stage ^ " [" ^ d.construct ^ "]: " ^ d.reason) | _ -> None)
let fail at construct reason = raise (Unsupported {stage="data"; location=at; construct; reason})
let parameter_name ctx name = Context.generated_name ctx.Context.profile "param" name
let type_name ctx name = match Context.find ctx ~namespace:"type" name with
  | Some d -> d.generated_name
  | None -> fail no_region "VarT" ("unknown type " ^ name)
let atom_key atom = Yojson.Safe.to_string (Domain.Atom.to_yojson atom.it)
let rec mixop_key = function
  | Domain.Mixfix.Arg () -> "A"
  | Domain.Mixfix.Atom a -> "K(" ^ atom_key a ^ ")"
  | Domain.Mixfix.Brack (a,m,b) -> "B(" ^ atom_key a ^ "," ^ mixop_key m ^ "," ^ atom_key b ^ ")"
  | Domain.Mixfix.Infix (a,m,b) -> "I(" ^ mixop_key a ^ "," ^ atom_key m ^ "," ^ mixop_key b ^ ")"
  | Domain.Mixfix.Seq ms -> "S(" ^ String.concat "," (List.map mixop_key ms) ^ ")"
let constructor_name ctx name mixop =
  let cases=match Context.find ctx ~namespace:"type" name with
    |Some {definition={it=Al.TypD(_,_,{it=Il.VariantT cs;_},_);_};_}->cs
    |_->fail no_region "VariantT" ("not a variant: " ^ name) in
  let key=mixop_key mixop in
  let rec ordinal i=function
    |[]->fail no_region "CaseE" ("unknown constructor in "^name)
    |(t,_,_)::cs->if mixop_key(fst(Domain.Mixfix.split t.it))=key then i else ordinal(i+1)cs in
  Context.generated_name ctx.Context.profile "case" (name ^ ":" ^ string_of_int(ordinal 0 cases))
let record_constructor ctx name = Context.generated_name ctx.Context.profile "record" name
let extern_constructor ctx name = Context.generated_name ctx.Context.profile "extern" name
let field_name ctx name atom = Context.generated_name ctx.Context.profile "field" (name ^ ":" ^ atom_key atom)
let definition ctx name = match Context.find ctx ~namespace:"type" name with Some d -> d.definition | None -> fail no_region "VarT" ("unknown type " ^ name)
let fields ctx name = match (definition ctx name).it with Al.TypD (_,_,{it=Il.StructT fs;_},_) -> fs | _ -> []
let constructor_fields ctx name mixop = match (definition ctx name).it with
  | Al.TypD (_,_,{it=Il.VariantT cs;_},_) -> (match List.find_opt (fun (t,_,_) -> mixop_key (fst (Domain.Mixfix.split t.it)) = mixop_key mixop) cs with
      | Some (t,_,_) -> snd (Domain.Mixfix.split t.it) | None -> fail no_region "CaseE" ("unknown constructor in " ^ name))
  | _ -> fail no_region "CaseE" ("not a variant: " ^ name)
let rec substitute substitutions t =
  let go = substitute substitutions in
  let it = match t.it with
    | Il.VarT (id, []) when List.mem_assoc id.it substitutions -> (List.assoc id.it substitutions).it
    | Il.VarT (id, ts) -> Il.VarT (id,List.map go ts)
    | Il.TupleT ts -> Il.TupleT (List.map go ts)
    | Il.IterT (t,i) -> Il.IterT (go t,i)
    | Il.FuncT (ps,ts,t) -> let inner=List.filter(fun(name,_)->not(List.exists(fun p->p.it=name)ps))substitutions in
        Il.FuncT (ps,List.map (substitute inner) ts,substitute inner t)
    | x -> x in {t with it}
let unfold_alias ctx typ =
  let rec go seen t = match t.it with
    | Il.VarT (id,ts) when not (S.mem id.it seen) -> (match Context.find ctx ~namespace:"type" id.it with
        | Some {definition={it=Al.TypD (_,ps,{it=Il.PlainT rhs;_},_);_};_} ->
            if List.length ps <> List.length ts then fail t.at "VarT" "alias arity mismatch";
            go (S.add id.it seen) (substitute (List.map2 (fun p t -> p.it,t) ps ts) rhs)
        | _ -> t)
    | _ -> t in go S.empty typ
let rec type_of_al ctx ~parameters t = match t.it with
  | Il.BoolT -> Bool | Il.NumT `NatT -> Nat | Il.NumT `IntT -> Int | Il.TextT -> Text
  | Il.VarT (id,ts) -> if List.mem id.it parameters then (
      if ts <> [] then fail t.at "VarT" "type parameter applied to arguments";
      Type_parameter (parameter_name ctx id.it))
    else Named (type_name ctx id.it,List.map (type_of_al ctx ~parameters) ts)
  | Il.TupleT [] -> Unit
  | Il.TupleT ts -> Product (List.map (type_of_al ctx ~parameters) ts)
  | Il.IterT (t,Il.List) -> List (type_of_al ctx ~parameters t)
  | Il.IterT (t,Il.Opt) -> Option (type_of_al ctx ~parameters t)
  | Il.FuncT (ps,ts,t) -> let parameters = List.map (fun p -> p.it) ps @ parameters in
      Function_ref {parameters=List.map (parameter_name ctx) (List.map (fun p->p.it) ps);
        inputs=List.map (type_of_al ctx ~parameters) ts; output=type_of_al ctx ~parameters t}
let rec dependencies = function
  | Named (n,ts) -> List.fold_left (fun s t -> S.union s (dependencies t)) (S.singleton n) ts
  | Product ts -> List.fold_left (fun s t -> S.union s (dependencies t)) S.empty ts
  | List t | Option t -> dependencies t
  | Function_ref {inputs;output;_} -> List.fold_left (fun s t -> S.union s (dependencies t)) (dependencies output) inputs
  | _ -> S.empty
let declaration_name = function Alias (n,_,_) | Inductive(n,_,_) | Record(n,_,_) -> n
let declaration_parameters = function Alias(_,ps,_) | Inductive(_,ps,_) | Record(_,ps,_) -> ps
let declaration_dependencies = function
  | Alias(_,_,t) -> dependencies t
  | Inductive(_,_,cs) -> List.fold_left (fun s c -> List.fold_left (fun s t -> S.union s (dependencies t)) s c.fields) S.empty cs
  | Record(_,_,fs) -> List.fold_left (fun s (b:binding) -> S.union s (dependencies b.typ)) S.empty fs
let lower ctx = try
  let declarations = List.filter_map (fun (d:Context.declaration) -> match d.definition.it with
    | Al.ExternTypD (id,_) -> Some (Inductive (d.generated_name,[],[{constructor_name=extern_constructor ctx id.it; fields=[]}]))
    | Al.TypD (id,ps,t,_) -> let source_ps=List.map (fun p -> p.it) ps in let ps=List.map (parameter_name ctx) source_ps in
        let lower = type_of_al ctx ~parameters:source_ps in
        Some (match t.it with
          | Il.PlainT rhs -> Alias(d.generated_name,ps,lower rhs)
          | Il.StructT fs -> Record(d.generated_name,ps,List.map (fun (a,t) -> {name=field_name ctx id.it a;typ=lower t}) fs)
          | Il.VariantT cs -> Inductive(d.generated_name,ps,List.map (fun (t,_,_) -> let mixop,ts=Domain.Mixfix.split t.it in {constructor_name=constructor_name ctx id.it mixop;fields=List.map lower ts}) cs))
    | _ -> None) ctx.Context.declarations in
  let by_name = List.fold_left (fun m d -> M.add (declaration_name d) d m) M.empty declarations in
  (* Tarjan visits declaration and edge orders deterministically. Its output is
     dependency first, so each emitted SCC only refers backward or internally. *)
  let index = ref 0 and stack = ref [] and result = ref [] in
  let indices=Hashtbl.create 100 and low=Hashtbl.create 100 and active=Hashtbl.create 100 in
  let rec visit name =
    let i = !index in incr index; Hashtbl.add indices name i; Hashtbl.add low name i;
    stack := name :: !stack; Hashtbl.replace active name true;
    S.iter (fun dep -> if M.mem dep by_name then
      if not (Hashtbl.mem indices dep) then (visit dep; Hashtbl.replace low name (min (Hashtbl.find low name) (Hashtbl.find low dep)))
      else if Option.value ~default:false (Hashtbl.find_opt active dep) then Hashtbl.replace low name (min (Hashtbl.find low name) (Hashtbl.find indices dep))) (declaration_dependencies (M.find name by_name));
    if Hashtbl.find low name = i then (
      let rec pop acc = match !stack with [] -> assert false | x::xs -> stack:=xs; Hashtbl.replace active x false;
        let acc=M.find x by_name::acc in if x=name then acc else pop acc in
      result := {module_name=Printf.sprintf "Types_%04d" (List.length !result);declarations=pop []} :: !result)
  in List.iter (fun d -> let n=declaration_name d in if not (Hashtbl.mem indices n) then visit n) declarations;
  Ok (List.rev !result)
with Unsupported d -> Error [d]
