open Util.Source
open Lang
open Coq_ir
module E=Lower_expr
exception Unsupported of diagnostic
let fail at construct reason=raise(Unsupported{stage="execution";location=at;construct;reason})
let shape = function []->Unit | [t]->t | ts->Product ts
let return_values values = E.ret {typ=shape(List.map(fun e->e.typ)values);term=Tuple values}
let bind_variable scope key value next =
  let binding={name=key;typ=value.typ} in E.local binding value (next(binding::scope))
let rec assign ctx scope pattern value (next:scope -> action) : action =
  match E.iter_variable pattern with
  | Some variable -> bind_variable scope (E.source_var_key variable) value next
  | None ->
    let decompose patterns constructor pattern_names =
      let variables=List.map2(fun e name->E.lit(E.note ctx e)(Render.identifier name))patterns pattern_names in
      let success=assign_many ctx scope patterns variables next in
      let exhaustive=match pattern.it with
        | Il.CaseE _ -> let name,_=E.variant ctx(pattern.note $ pattern.at) in
            (match (Data.definition ctx name).it with Al.TypD(_,_,{it=Il.VariantT [_];_},_)->true|_->false)
        | _->false in
      {result=success.result;node=Match(value,[constructor,success] @
        (if exhaustive then []else["_",E.error success.result "StructureError" "assignment structure mismatch"]))}
    in
    match pattern.it with
    | Il.TupleE patterns ->
        let names=List.map(fun _->E.fresh_name())patterns in
        let variables=List.map2(fun e name->E.lit(E.note ctx e)(Render.identifier name))patterns names in
        let success=assign_many ctx scope patterns variables next in
        {result=success.result;node=Match(value,[Render.tuple(List.map Render.identifier names),success])}
    | Il.CaseE notation ->
        let name,_=E.variant ctx (pattern.note $ pattern.at) in
        let mixop,patterns=Domain.Mixfix.split notation in
        let names=List.map(fun _->E.fresh_name())patterns in
        decompose patterns (String.concat " " (Data.constructor_name ctx name mixop::List.map Render.identifier names)) names
    | Il.StrE fields ->
        let name,ts=E.variant ctx(pattern.note $ pattern.at) in
        let values=List.map(fun(atom,p)->E.primitive(E.note ctx p)(Data.field_name ctx name atom)
          (List.map(fun t->E.lit Unit(Emit_data.render_type(E.typ ctx t)))ts@[value]))fields in
        assign_many ctx scope (List.map snd fields)values next
    | Il.OptE None -> decompose [] "None" []
    | Il.OptE(Some p) -> let name=E.fresh_name() in decompose [p]("Some "^Render.identifier name)[name]
    | Il.ListE ps -> let names=List.map(fun _->E.fresh_name())ps in decompose ps ("["^String.concat "; " (List.map Render.identifier names)^"]") names
    | Il.ConsE(a,b) -> let names=[E.fresh_name();E.fresh_name()] in decompose [a;b] (String.concat " :: " (List.map Render.identifier names))names
    | Il.IterE(inner,(kind,variables)) ->
        collect ctx scope kind variables value (fun scope element next -> assign ctx scope inner element next) next
    | _ -> fail pattern.at "assignment" ("AL binder is not invertible: " ^ Al.Print.string_of_exp pattern)
and assign_many ctx scope patterns values (next:scope -> action) : action = match patterns,values with
  | [],[] -> next scope
  | p::ps,v::vs -> assign ctx scope p v (fun scope->assign_many ctx scope ps vs next)
  | _ -> fail no_region "assignment" "pattern/value arity mismatch"
and collect ctx scope kind variables values action (next:scope -> action) : action =
  let element_types=List.map(fun(_,t,dims)->
    List.fold_left(fun t i->match i with Il.List->List t|Il.Opt->Option t)(E.typ ctx t)dims)variables in
  let keys=List.map(fun(id,_,dims)->E.source_var_key(id,dims))variables in
  let output_bindings=List.map2(fun(id,_,dims) typ->{name=E.source_var_key(id,dims@[kind]);typ=(match kind with Il.List->List typ|Il.Opt->Option typ)})variables element_types in
  let item_type=match E.unfold_type ctx values.typ with List t|Option t->t|_->fail no_region "iteration" "expected an option/list" in
  let item={name=E.fresh_name();typ=item_type} in
  let inner=action scope (E.var item)(fun scope -> return_values(List.map(fun key->E.find_variable scope no_region key)keys)) in
  let gathered = match kind with
    | Il.List -> {result=List inner.result;node=Traverse(item,values,inner)}
    | Il.Opt -> let name=Render.identifier item.name in
        {result=Option inner.result;node=Match(values,["None",E.ret(E.lit(Option inner.result)"None");
           "Some "^name,E.using inner(fun v->E.ret(E.primitive(Option v.typ)"Some"[v]))])} in
  E.using gathered(fun gathered ->
    let names=List.map(fun _->E.fresh_name())variables in
    let projections=List.mapi(fun index typ ->
      let row_name=E.fresh_name() in
      let projection="(fun " ^ Render.identifier row_name ^ " => match " ^ Render.identifier row_name ^ " with " ^ Render.tuple(List.map Render.identifier names) ^ " => " ^ Render.identifier(List.nth names index) ^ " end)" in
      E.primitive (match kind with Il.List->List typ|Il.Opt->Option typ)
        (match kind with Il.List->"map " ^ projection|Il.Opt->"option_map " ^ projection) [gathered])element_types in
    List.fold_right2(fun b value result->E.local b value result)output_bindings projections (next(output_bindings@scope)))
let rec prems ctx scope premises (next:scope -> action) : action = match premises with []->next scope | p::ps -> prem ctx scope p (fun scope->prems ctx scope ps next)
and prem ctx scope p (next:scope -> action) : action =
  match p.it with
  | Il.IfPr exp -> E.using(E.lower_exn ctx scope exp)(fun v->E.guard v (next scope))
  | Il.DebugPr exp -> E.using(E.lower_exn ctx scope exp)(fun _->next scope)
  | Il.LetPr(pattern,expression) -> E.using(E.lower_exn ctx scope expression)(fun v->assign ctx scope pattern v next)
  | Il.RulePr(id,notation,inputs) ->
      let declaration=match Context.find ctx ~namespace:"rel" id.it with Some d->d|None->fail id.at "RulePr" "unknown relation" in
      let signature=Option.get declaration.signature in
      let expressions=Domain.Mixfix.args notation in
      let input_exps=List.filteri(fun index _->List.mem index inputs)expressions in
      let outputs=List.filteri(fun index _->not(List.mem index inputs))expressions in
      let result=shape(List.map(E.typ ctx)signature.output_types) in
      E.using_all(List.map(E.lower_exn ctx scope)input_exps)(fun arguments ->
        let invoke={result;node=Invoke{target=declaration.generated_name;type_arguments=[];arguments;result}} in
        E.using invoke(fun value->
          match outputs with
          | []->next scope | [p]->assign ctx scope p value next
          | _ -> assign ctx scope (Il.TupleE outputs $$ (p.at,Il.TupleT(List.map(fun e->e.note $ e.at)outputs))) value next))
  | Il.IfHoldPr(id,notation) | Il.IfNotHoldPr(id,notation) ->
      let declaration=match Context.find ctx ~namespace:"rel" id.it with Some d->d|None->fail id.at "hold" "unknown relation" in
      let signature=Option.get declaration.signature in
      let expressions=Domain.Mixfix.args notation in
      E.using_all(List.map(E.lower_exn ctx scope)expressions)(fun arguments ->
        if List.length arguments<>List.length signature.input_positions then
          E.error (next scope).result "StructureError" "hold relation argument arity mismatch"
        else let result=shape(List.map(E.typ ctx)signature.output_types) in
          let invoke={result;node=Invoke{target=declaration.generated_name;type_arguments=[];arguments;result}} in
          let invoke=match p.it with Il.IfNotHoldPr _->{result=Unit;node=Negate invoke}|_->invoke in
          E.using invoke(fun _->next scope))
  | Il.IterPr(premise,(kind,bound,binding)) ->
      (* Build subcontexts from the original outer scope, then collect only the
         new binding variables. Traverse threads fresh in source order. *)
      let keys=List.map(fun(id,_,dims)->E.source_var_key(id,dims))bound in
      let collections=List.map(fun(id,_,dims)->E.find_variable scope p.at(E.source_var_key(id,dims@[kind])))bound in
      if collections=[] then fail p.at "IterPr" "iteration extent has no bound variable";
      let types=List.map(fun value->match E.unfold_type ctx value.typ with List t|Option t->t|_->fail p.at "IterPr" "wrong bound iteration type")collections in
      let locals=List.map2(fun name typ->{name;typ})keys types in
      let names=List.map(fun _->E.fresh_name())locals in
      let element_type=shape types in
      let context_body scope row next =
        let scoped=locals@scope in
        let body=prem ctx scoped premise next in
        let body=List.fold_right2(fun b name body->E.local b (E.lit b.typ(Render.identifier name)) body)locals names body in
        {result=body.result;node=Match(row,[Render.tuple(List.map Render.identifier names),body])} in
      let zip collections=match collections with
        | first::rest->fst(List.fold_left(fun(acc,ts) value->
            let t=match E.unfold_type ctx value.typ with List t->t|_->assert false in let ts=ts@[t] in
            E.primitive(List(shape ts)) "combine"[acc;value],ts)(first,[List.hd types])rest)
        | []->assert false in
      (match kind with
      | Il.List -> let zipped=zip collections in
          let body=collect ctx scope kind binding zipped context_body next in
          let first=List.hd collections in
          List.fold_right(fun xs (body:action) ->
            {result=body.result;node=Match(E.primitive Bool "Nat.eqb"[E.primitive Nat "List.length"[first];E.primitive Nat "List.length"[xs]],
               ["true",body;"false",E.error body.result "StructureError" "premise iteration lengths differ"])}) (List.tl collections)body
      | Il.Opt ->
          let option_type=Option element_type in
          let options={typ=Product(List.map(fun e->e.typ)collections);term=Tuple collections} in
          let none=collect ctx scope kind binding (E.lit option_type "None") context_body next in
          let values=List.map2(fun name typ->E.lit typ(Render.identifier name))names types in
          let some=collect ctx scope kind binding(E.primitive option_type "Some"[{typ=element_type;term=Tuple values}])context_body next in
          {result=none.result;node=Match(options,[Render.tuple(List.map(fun _->"None")names),none;
             Render.tuple(List.map(fun name->"Some " ^ Render.identifier name)names),some] @
             (if List.length names>1 then ["_",E.error none.result "StructureError" "premise iteration options differ"]else[]))})
let lower ctx = try
  E.counter:=0; Casts.reset ();
  let bodies=List.filter_map(fun(d:Context.declaration)->match d.signature with
    | None -> None
    | Some signature ->
      let parameters=List.mapi(fun index position->{name="#arg" ^ string_of_int index;typ=E.typ ctx(List.nth signature.argument_types position)})signature.input_positions in
      let values=List.map E.var parameters in
      let result=shape(List.map(E.typ ctx)signature.output_types) in
      let function_clause clause = let args,expression,premises=clause.it in
        let rec assign_args args values scope next = match args,values with
          | [],[]->next scope
          | {it=Il.ExpA pattern;_}::args,value::values -> assign ctx scope pattern value(fun scope->assign_args args values scope next)
          | {it=Il.DefA id;_}::args,value::values -> bind_variable scope ("$" ^ id.it)value(fun scope->assign_args args values scope next)
          | _->fail clause.at "clause" "argument arity mismatch" in
        assign_args args values [] (fun scope->prems ctx scope premises(fun scope->E.lower_exn ctx scope expression)) in
      let rule_path (_,patterns,common) (_,premises,outputs) =
        assign_many ctx [] patterns values(fun scope->prems ctx scope(common@premises)(fun scope->
          E.using_all(List.map(E.lower_exn ctx scope)outputs)return_values)) in
      let action=match d.definition.it with
        | Al.ExternRelD _ | Al.ExternDecD _ -> {result;node=Choose result}
        | Al.FuncDecD(_,_,_,_,clauses,otherwise,_) ->
            {result;node=Alternatives(List.map function_clause clauses @ Option.to_list(Option.map function_clause otherwise))}
        | Al.RelD(_,_,_,groups,otherwise,_) ->
            let paths=List.concat_map(fun group->let _,matching,paths=group.it in List.map(rule_path matching)paths)groups in
            let other=Option.map(fun g->let _,matching,path=g.it in rule_path matching path)otherwise in
            {result;node=Alternatives(paths @ Option.to_list other)}
        | Al.TableDecD(_,_,_,rows,_) ->
            let clauses=List.map(fun row->let _,args,output,ps=row.it in (args,output,ps)$row.at)rows in
            {result;node=Alternatives(List.map function_clause clauses)}
        | Al.BuiltinDecD _ -> Builtins.lower_exn ctx d parameters
        | _->assert false in
      Some{call_name=d.generated_name;parameters;result;action})ctx.Context.declarations in
  Ok bodies
with Unsupported d | E.Unsupported d | Data.Unsupported d | Builtins.Unsupported d -> Error[d]
