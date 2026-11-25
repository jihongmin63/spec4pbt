(* Property witnesses are built from typed AL, before ordinary relation lowering.
   Existing relations are left untouched. A non-call premise becomes one small
   AL relation, lowered by the same backend as every source relation. *)
open Util.Source
open Lang
open Lang.Il
open Lang.Al
module Mixfix = Domain.Mixfix

type call = { name : string; inputs : exp list; outputs : exp list;
              temporary : bool; source_at : region }
type plan = { pre : string; inputs : exp list; variables : exp list;
              calls : call list }

let fail at reason = Data.fail at "property" reason
let variable exp = match exp.it with VarE id -> id.it
  | _ -> fail exp.at "property input must be a variable"
let unique variables = List.fold_left (fun found exp ->
  if List.exists (fun e -> variable e = variable exp) found then found
  else found @ [exp]) [] variables
let collector =
  let module C = Al.Walk.Collect in
  let base = C.make_base ~default:[] ~compose:( @ ) in
  {base with C.collect_exp = (fun c exp -> match exp.it with
    | VarE _ -> [exp] | _ -> C.default_collect_exp c exp)}
let vars_prem prem = Al.Walk.Collect.collect_prem collector prem |> unique
let vars_exp exp = Al.Walk.Collect.collect_exp collector exp |> unique

let prepare spec pre =
  let definition = List.find_opt (fun def -> match def.it with
    | RelD (id, _, _, _, _, _) -> id.it = pre | _ -> false) spec in
  let definition = match definition with Some d -> d
    | None -> fail no_region (pre ^ " has no specification definition") in
  let inputs, prems, returned = match definition.it with
    | RelD (_, _, _, [{it=(_, (_, inputs, common), [(_, prems, outputs)]);_}], None, _) ->
        inputs, common @ prems, outputs
    | _ -> fail definition.at "Pre must have exactly one rule" in
  List.iter (fun exp -> ignore(variable exp)) inputs;
  if List.length (unique inputs) <> List.length inputs then
    fail definition.at "Pre inputs must be distinct variables";
  let variables = ref inputs and known = ref inputs and added = ref [] and calls = ref [] in
  let names xs = List.map variable xs in
  let fresh_name index = "PropertyPremise" ^ pre ^ string_of_int index in
  let ensure_name name = if List.exists (fun def -> match def.it with
    | RelD(id,_,_,_,_,_) | ExternRelD(id,_,_,_) -> id.it=name | _ -> false) spec
    then fail definition.at ("temporary relation name collision: " ^ name) in
  let append (call : call) =
    variables := unique (!variables @ call.inputs @ call.outputs);
    known := unique (!known @ call.outputs); calls := !calls @ [call] in
  let temporary index at prems inputs outputs =
    let name = fresh_name index in ensure_name name;
    let id = name $ at in
    let args = inputs @ outputs in
    let nottyp = Mixfix.Seq (List.map (fun exp -> Mixfix.Arg (exp.note $ exp.at)) args) $ at in
    let path = ("main" $ at), prems, outputs in
    let group = (id, (args, inputs, []), [path]) $ at in
    added := !added @ [RelD(id,nottyp,List.init(List.length inputs) Fun.id,[group],None,[]) $ at];
    {name;inputs;outputs;temporary=true;source_at=at} in
  List.iteri (fun index prem ->
    (match prem.it with
     | IterPr _ -> fail prem.at "iteration is outside property scope"
     | _ -> ());
    let vars = vars_prem prem in
    let ins, outs = List.partition (fun exp -> List.mem (variable exp) (names !known)) vars in
    let call = match prem.it with
      | RulePr(id,notexp,hints) when List.for_all (fun exp -> match exp.it with VarE _->true|_->false) (Mixfix.args notexp) ->
          let inputs,outputs = Hints.Input.split hints (Mixfix.args notexp) in
          {name=id.it;inputs;outputs;temporary=false;source_at=prem.at}
      | _ -> temporary index prem.at [prem] ins outs in
    append call) prems;
  (* Returning an expression can fail or consume fresh state. Keep that work
     even though property outputs are existential and are not transported. *)
  if List.exists (fun exp -> match exp.it with VarE _->false|_->true) returned then begin
    let index = List.length prems in
    let ins = unique (List.concat_map vars_exp returned) in
    let outputs = List.mapi (fun i exp ->
      VarE (("#property_return" ^ string_of_int i) $ exp.at) $$ (exp.at,exp.note)) returned in
    let call = temporary index definition.at [] ins returned in
    (* The translated relation computes the source return expressions; its
       application binds fresh constructor witnesses in the property. *)
    append {call with outputs}
  end;
  spec @ !added, {pre;inputs;variables= !variables;calls= !calls}

let coq_var exp = "w_" ^ String.concat "" (List.init (String.length (variable exp))
  (fun i -> Printf.sprintf "%02x" (Char.code (variable exp).[i])))

let wire_type ctx typ =
  let typ = Data.unfold_alias ctx typ in
  match typ.it with
  | BoolT -> "bool" | NumT `NatT -> "nat" | NumT `IntT -> "int" | TextT -> "text"
  | VarT(id,[]) -> id.it
  | _ -> fail typ.at ("unsupported property wire type: " ^ Al.Print.string_of_typ typ)

let type_schema ctx roots =
  let found = ref [] in
  let rec visit typ =
    let typ = Data.unfold_alias ctx typ in
    match typ.it with
    | BoolT | NumT _ | TextT -> ()
    | VarT(id,[]) when List.mem_assoc id.it !found -> ()
    | VarT(id,[]) ->
        let cases = match (Data.definition ctx id.it).it with
          | TypD(_,[],{it=VariantT cases;_},_) -> cases
          | _ -> fail typ.at ("property codec requires a concrete variant: " ^ id.it) in
        found := !found @ [id.it, `Null];
        let constructors = List.map (fun (nottyp,_,_) ->
          let mixop,fields = Mixfix.split nottyp.it in
          List.iter visit fields;
          (* Keep the plain prefix convention only when it is unambiguous.
             Every other ID retains the complete structural operator shape. *)
          let simple_prefix mixop =
            let atom a = match a.it with
              | Domain.Atom.Keyword name -> Some name
              | Domain.Atom.Tag name -> Some("_" ^ name)
              | _ -> None in
            match mixop with
            | Mixfix.Atom a -> atom a
            | Mixfix.Seq(Mixfix.Atom a :: args)
              when List.for_all(function Mixfix.Arg()->true|_->false)args -> atom a
            | _ -> None in
          let token = match simple_prefix mixop with
            | Some name when List.length(List.filter(fun(nottyp,_,_)->
                simple_prefix(fst(Mixfix.split nottyp.it))=Some name)cases)<=1 -> name
            | _ -> "mixfix:" ^ Data.mixop_key mixop in
          `Assoc["name",`String token; "coq_name",`String(Data.constructor_name ctx id.it mixop);
                 "fields",`List(List.map(fun t->`String(wire_type ctx t))fields)]) cases in
        let schema = `Assoc["coq_type",`String(Data.type_name ctx id.it);"constructors",`List constructors] in
        found := List.map(fun(name,value)->name,if name=id.it then schema else value) !found
    | _ -> fail typ.at ("unsupported property wire type: " ^ Al.Print.string_of_typ typ)
  in List.iter visit roots; `Assoc !found

let to_json ctx plan =
  let field exp = `Assoc["name",`String(variable exp);"coq_name",`String(coq_var exp);
    "type",`String(wire_type ctx (exp.note $ exp.at));
    "coq_type",`String(Emit_data.render_type(Lower_expr.typ ctx (Data.unfold_alias ctx (exp.note $ exp.at))))] in
  let call (c : call) =
    let d=Option.get(Context.find ctx ~namespace:"rel" c.name) in
    `Assoc["name",`String c.name;"relation",`String(d.generated_name ^ "_execute");
      "inputs",`List(List.map(fun e->`String(coq_var e))c.inputs);
      "outputs",`List(List.map(fun e->`String(coq_var e))c.outputs);
      "temporary",`Bool c.temporary;"source",`String(string_of_region c.source_at)] in
  `Assoc["precondition",`String plan.pre;"namespace",`String(Emit.namespace ctx);
    "inputs",`List(List.map field plan.inputs);"variables",`List(List.map field plan.variables);
    "calls",`List(List.map call plan.calls);
    "type_schema",type_schema ctx (List.map(fun e->e.note $ e.at) plan.variables)]
