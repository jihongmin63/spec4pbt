(* Native, typed partial conversions.  The registry is per translation and is
   deliberately independent of source declaration names.  Subtype guards use
   the same conversion, but executable casts must report None as an error. *)
open Util.Source
open Lang
open Coq_ir
type request = { source : typ; target : typ; name : string; parameters : string list }
let requests : request list ref = ref []
let reset () = requests := []
let rec free = function
  | Type_parameter p -> [p]
  | Named (_, ts) | Product ts -> List.concat_map free ts
  | List t | Option t -> free t
  | Function_ref {parameters;inputs;output} ->
      List.filter (fun p -> not (List.mem p parameters)) (List.concat_map free (output::inputs))
  | _ -> []
let register ctx source target =
  match List.find_opt (fun r -> r.source=source && r.target=target) !requests with
  | Some r -> r
  | None ->
      let r={source;target;name=Context.generated_name ctx.Context.profile "cast" (string_of_int (List.length !requests));
        parameters=List.sort_uniq String.compare (free source @ free target)} in
      requests := !requests @ [r];r
let head r = Emit_data.apply r.name r.parameters
let request ctx ~source ~target =
  let rec parameters t = match t.it with
    | Il.VarT (id, ts) ->
        (if Context.find ctx ~namespace:"type" id.it=None then [id.it] else []) @ List.concat_map parameters ts
    | Il.TupleT ts -> List.concat_map parameters ts
    | Il.IterT (t,_) -> parameters t
    | Il.FuncT (ps,ts,t) -> List.filter(fun p->not(List.exists(fun q->p=q.it)ps))(List.concat_map parameters (t::ts))
    | _ -> [] in
  let parameters=List.sort_uniq String.compare (parameters source @ parameters target) in
  head (register ctx (Data.type_of_al ctx ~parameters source) (Data.type_of_al ctx ~parameters target))

let render ctx modules =
  let declarations=List.concat_map (fun m->m.declarations) modules in
  let find n=List.find (fun d->Data.declaration_name d=n) declarations in
  let rec expand seen = function
    | Named(n,ts) as t -> (match find n with
        | Alias(_,ps,rhs) when not(List.mem n seen) -> expand (n::seen) (Emit_data.replace (List.combine ps ts) rhs)
        | _ -> t)
    | t -> t in
  let equal t u =
    let rec normalize t=match expand [] t with
      | Named(n,ts)->Named(n,List.map normalize ts)
      | List t->List(normalize t) | Option t->Option(normalize t)
      | Product ts->Product(List.map normalize ts)
      | t->t in normalize t=normalize u in
  let source n=Emit_data.source ctx n in
  let constructors n ts = match find n with
    | Inductive(_,ps,cs) ->
        List.map(fun c->{c with fields=List.map (Emit_data.replace(List.combine ps ts)) c.fields})cs
    | _ -> [] in
  let mixop n c = match (source n).definition.it with
    | Al.TypD(_,_,{it=Il.VariantT cs;_},_) ->
        let t,_,_=List.find(fun(t,_,_)->Data.constructor_name ctx (source n).source_name (fst(Domain.Mixfix.split t.it))=c.constructor_name)cs in
        Some (Data.mixop_key(fst(Domain.Mixfix.split t.it)))
    | _ -> None in
  let active_names=ref [] in
  let nested=ref [] and fresh=ref 0 in
  let next prefix=let n= !fresh in incr fresh;prefix ^ string_of_int n in
  let rec contains_active t=match expand [] t with
    | Named(n,ts)->List.mem n !active_names || List.exists contains_active ts
    | Product ts->List.exists contains_active ts
    | List t|Option t->contains_active t | _->false in
  let some x=Emit_data.apply "Some" [x] in
  let sequence expressions finish =
    let names=List.map(fun _->next "converted")expressions in
    List.fold_right2(fun e name tail->"match "^e^" with None => None | Some "^name^" => "^tail^" end")expressions names (finish names) in
  let rec convert source target value =
    let source=expand [] source and target=expand [] target in
    if equal source target then some value else match source,target with
    | Nat,Int -> some(Emit_data.apply "Z.of_nat" [value])
    | Int,Nat -> "if Z.leb 0 "^Emit_data.par value^" then "^some(Emit_data.apply "Z.to_nat" [value])^" else None"
    | List t,List u ->
        let walk=next "cast_list" and xs=next "xs" and x=next "x" and tail=next "tail" in
        let body=sequence [convert t u x;Emit_data.apply walk [tail]] (function [x;xs]->some(x^" :: "^xs)|_->assert false) in
        Emit_data.apply (Emit_data.par("fix "^walk^" ("^xs^" : list "^Emit_data.par(Emit_data.render_type t)^") : option (list "^Emit_data.par(Emit_data.render_type u)^") := match "^xs^" with [] => Some [] | "^x^" :: "^tail^" => "^body^" end")) [value]
    | Option t,Option u -> let x=next "option_value" in
        "match "^value^" with None => Some None | Some "^x^" => "^sequence[convert t u x](function[x]->some(some x)|_->assert false)^" end"
    | Product ts,Product us when List.length ts=List.length us ->
        let xs=List.map(fun _->next "tuple_value")ts in
        "match "^value^" with "^Emit_data.tuple_pattern xs^" => "^
        sequence(List.map2(fun (t,u) x->convert t u x)(List.combine ts us)xs)(fun xs->some(Emit_data.tuple_pattern xs))^" end"
    | Named(n,ts),Named(m,us) ->
        (match find n,find m with
        | Inductive _,Inductive _ ->
            if List.exists contains_active ts then nested_conversion source target value n ts m us
            else Emit_data.apply (head(register ctx source target)) [value]
        | _ -> "None") (* Records are invariant in the source interpreter. *)
    | _ -> "None"
  and variant_body source target value n ts m us =
    let targets=constructors m us in
    let branches=List.map(fun c->
      let xs=List.map(fun _->next "field")c.fields in
      let pattern=String.concat " " (c.constructor_name :: xs) in
      let matched=List.find_opt(fun d->match mixop n c,mixop m d with Some a,Some b->a=b|_->false)targets in
      let term=match matched with
        | Some d when List.length c.fields=List.length d.fields ->
            sequence(List.map2(fun(t,u)x->convert t u x)(List.combine c.fields d.fields)xs)
              (fun xs->some(Emit_data.apply ("@" ^ d.constructor_name) (List.map Emit_data.render_type us @ xs)))
        | _ -> "None" in
      "| "^pattern^" => "^term)(constructors n ts) in
    ignore source;ignore target;
    "match "^value^" with "^String.concat " " branches^" end"
  and nested_conversion source target value n ts m us =
    match List.find_opt(fun(t,u,_)->t=source && u=target) !nested with
    | Some(_,_,name)->Emit_data.apply name [value]
    | None ->
        let name=next "cast_nested" in nested := (source,target,name)::!nested;
        let body=variant_body source target "nested_value" n ts m us in
        nested:=List.tl !nested;
        Emit_data.apply(Emit_data.par("fix "^name^" (nested_value : "^Emit_data.render_type source^") : option "^Emit_data.par(Emit_data.render_type target)^" := "^body))[value]
  in
  let body r =
    let t=expand [] r.source and u=expand [] r.target in
    if equal t u then some "value" else match t,u with
    | Named(n,ts),Named(m,us) -> (match find n,find m with
        | Inductive _,Inductive _ -> variant_body t u "value" n ts m us
        | _->convert t u "value")
    | _->convert t u "value" in
  (* Discover the closure before emitting.  Calling a generated conversion from
     a generic container can hide structural descent from Coq; containers that
     contain the active family are therefore traversed by a local fixpoint. *)
  let group_of r = match expand [] r.source with
    | Named(n,_) -> List.find_opt(fun m->List.exists(fun d->Data.declaration_name d=n)m.declarations)modules
    | _->None in
  let family r=match group_of r with None->[]|Some m->List.map Data.declaration_name m.declarations in
  let rec discover index = if index<List.length !requests then (
    let r=List.nth !requests index in active_names:=family r;ignore(body r);discover(index+1)) in
  discover 0;
  (* Dependencies between source families follow the already topologically
     sorted data modules.  Non-native root requests are emitted afterwards. *)
  let ordered=List.concat_map(fun m->List.filter(fun r->match group_of r with Some g->g.module_name=m.module_name|_->false)!requests)modules @
    List.filter(fun r->group_of r=None)!requests in
  let emitted=Hashtbl.create 30 and b=Buffer.create 10000 in
  let line s=Buffer.add_string b(s^"\n") in
  let render_group rs =
    match rs with []->()|first::_->
      active_names:=family first;
      let recursive=List.exists(fun r->let t=expand [] r.source in match t with
        |Named(n,_)->Data.S.mem n (List.fold_left(fun deps d->Data.S.union deps (Data.declaration_dependencies d))Data.S.empty
            (match group_of r with None->[]|Some m->m.declarations))
        |_->false)rs in
      List.iteri(fun i r->
        let prefix=if recursive then (if i=0 then "Fixpoint " else "with ") else "Definition " in
        let signature=prefix^r.name^" "^Emit_data.params r.parameters^" (value : "^Emit_data.render_type r.source^")"^
          (if recursive then " {struct value}" else "")^" : option "^Emit_data.par(Emit_data.render_type r.target)^" := " in
        line(signature^body r^(if recursive then "" else ".")))rs;
      if recursive then line "." in
  List.iter(fun r->if not(Hashtbl.mem emitted r.name)then(
    let rs=match group_of r with
      |Some group->List.filter(fun x->match group_of x with Some g->g.module_name=group.module_name|_->false)ordered
      |None->[r] in
    List.iter(fun r->Hashtbl.add emitted r.name())rs;render_group rs))ordered;
  Buffer.contents b
