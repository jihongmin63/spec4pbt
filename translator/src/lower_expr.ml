open Util.Source
open Lang
open Coq_ir
exception Unsupported of diagnostic
let fail at construct reason = raise(Unsupported{stage="expression";location=at;construct;reason})
let parameter_cache = ref None
let parameters ctx = match !parameter_cache with
  | Some (previous,values) when previous == ctx -> values
  | _ -> let values=List.concat_map (fun (d:Context.declaration) -> match d.signature with
      | None -> [] | Some s -> List.map (fun p->p.it) s.type_parameters) ctx.Context.declarations |> List.sort_uniq String.compare in
      parameter_cache:=Some(ctx,values);values

let typ ctx t = Data.type_of_al ctx ~parameters:(parameters ctx) t
let unfold_type ctx original =
  let rec unfold seen = function
    | Named(name,arguments) as t when not(List.mem name seen) ->
        (match Context.String_map.find_opt name ctx.Context.by_generated_name with
        | Some {definition={it=Al.TypD(_,ps,{it=Il.PlainT rhs;_},_);_};_} ->
            let source_ps=List.map(fun p->p.it)ps in
            let body=Data.type_of_al ctx ~parameters:source_ps rhs in
            let substitutions=List.map2(fun p argument->Data.parameter_name ctx p,argument)source_ps arguments in
            unfold(name::seen)(Emit_data.replace substitutions body)
        | _->t)
    | t->t in unfold [] original
let is_text ctx t = unfold_type ctx t=Text
let record_fields ctx name arguments =
  match (Data.definition ctx name).it with
  | Al.TypD(_,ps,_,_) -> List.map(fun(atom,t)->atom,Data.substitute(List.map2(fun p t->p.it,t)ps arguments)t)(Data.fields ctx name)
  | _->Data.fields ctx name

let numeric_operand ctx optyp value =
  if optyp = `IntT && unfold_type ctx value.typ = Nat then
    {typ=Int;term=Primitive("Z.of_nat",[value])} else value

let note ctx e = typ ctx (e.note $ e.at)
let lit typ code = {typ;term=Literal code}
let var (b:binding) = {typ=b.typ;term=Variable b.name}
let ret (e:expression) = {result=e.typ;node=Return e}
let primitive typ name args = {typ;term=Primitive(name,args)}
let error result kind message = {result;node=Error("{| error_kind := " ^ kind ^ "; error_detail := " ^ Emit_data.quote message ^ " |}")}
let guard condition (continuation:action) = {result=continuation.result;node=Bind({name="#guard";typ=Unit},{result=Unit;node=Guard condition},continuation)}
let bind (name:binding) (left:action) (right:action) = {result=right.result;node=Bind(name,left,right)}
let local (name:binding) value (right:action) = {result=right.result;node=Local(name,value,right)}
let counter = ref 0
let fresh_name () = let n= !counter in incr counter; "#temp" ^ string_of_int n
let using (left:action) next = let b={name=fresh_name();typ=left.result} in bind b left (next (var b))
let rec using_all actions next = match actions with []->next [] | a::xs -> using a (fun v->using_all xs (fun vs->next(v::vs)))
let option_result ?(kind="ALAbort") result option =
  let name=fresh_name() in {result;node=Match(option,["Some " ^ Render.identifier name,ret(lit result (Render.identifier name));
    "None",error result kind "partial expression failed"])}
let source_var_key (id,iters) = id.it ^ String.concat "" (List.map(function Il.List->"*" | Il.Opt->"?")iters)
let rec iter_variable e = match e.it with
  | Il.VarE id -> Some(id,[])
  | Il.IterE(inner,(it,[(id,_,dims)])) -> (match iter_variable inner with
      | Some(i,ds) when i.it=id.it && ds=dims -> Some(i,ds@[it]) | _->None)
  | _->None
let find_variable scope at key = match List.find_opt(fun(b:binding)->b.name=key)scope with
  | Some b->var b | None->fail at "VarE" ("unbound variable " ^ key)
let variant ctx t = match (Data.unfold_alias ctx t).it with
  | Il.VarT(id,ts) -> id.it,ts | _->fail t.at "variant" "expected a declared variant/record type"
let rec lower_exn ctx scope e : action =
  let result=note ctx e in let lower=lower_exn ctx scope in
  match iter_variable e with
  | Some var -> ret(find_variable scope e.at (source_var_key var))
  | None -> match e.it with
  | Il.BoolE value -> ret(lit result (string_of_bool value))
  | Il.NumE (`Nat n) -> ret(lit result ("(" ^ Bigint.to_string n ^ ")%nat"))
  | Il.NumE (`Int n) -> ret(lit result ("(" ^ Bigint.to_string n ^ ")%Z"))
  | Il.TextE value -> ret(lit result (Emit_data.quote value))
  | Il.VarE _ -> assert false
  | Il.UnE(op,_,x) -> using(lower x)(fun x->ret(primitive result (match op with `NotOp->"negb"|`PlusOp->"(fun x => x)"|`MinusOp->
      (if unfold_type ctx x.typ=Nat then "(fun n => Z.opp (Z.of_nat n))" else "Z.opp")) [x]))
  | Il.BinE(op,optyp,a,b) -> using_all [lower a;lower b](function
      | [a;b] -> let a=numeric_operand ctx optyp a and b=numeric_operand ctx optyp b in
        let int=optyp=`IntT in
        (match op with
        | `DivOp | `ModOp -> option_result ~kind:"HostConversion" result (primitive (Option result)
            (match op,int with `DivOp,false->"divide_nat"|`DivOp,true->"divide_int"|_,false->"remainder_nat"|_->"remainder_int") [a;b])
        | `PowOp -> error result "ALAbort" "PowOp is rejected by the pinned native numeric evaluator"
        | _ -> ret(primitive result (match op with
            | `AndOp->"andb"|`OrOp->"orb"|`ImplOp->"(fun a b => orb (negb a) b)"|`EquivOp->"Bool.eqb"
            | `AddOp->if int then "Z.add" else "Nat.add"
            | `SubOp->if int then "Z.sub" else "subtract_nat"
            | `MulOp->if int then "Z.mul" else "Nat.mul"|_->assert false)[a;b]))
      | _->assert false)
  | Il.CmpE(op,optyp,a,b) -> using_all[lower a;lower b](function
      | [a;b] -> let a=numeric_operand ctx optyp a and b=numeric_operand ctx optyp b in
        let cmp = match op with
          | `EqOp | `NeOp -> primitive Bool ("equal_value " ^ Emit_data.ops_expr a.typ)[a;b]
          | _ -> primitive Bool ((if optyp=`IntT then "Z." else "Nat.") ^
              (match op with `LtOp|`GtOp->"ltb"|`LeOp|`GeOp->"leb"|_->assert false))
              (if op=`GtOp || op=`GeOp then [b;a] else [a;b]) in
        ret(if op=`NeOp then primitive Bool "negb"[cmp] else cmp)
      | _->assert false)
  | Il.TupleE es -> using_all(List.map lower es)(fun values->ret{typ=result;term=Tuple values})
  | Il.ListE es -> using_all(List.map lower es)(fun values->ret(lit result ("[" ^ String.concat "; " (List.map Render.expression values) ^ "]")))
  | Il.OptE None -> ret(lit result "None")
  | Il.OptE(Some e) -> using(lower e)(fun v->ret(primitive result "Some"[v]))
  | Il.ConsE(a,b) | Il.CatE(a,b) -> using_all[lower a;lower b](function[a;b]->
      ret(primitive result (match e.it with Il.ConsE _->"cons"|_-> if is_text ctx a.typ then "String.append" else "List.app")[a;b])|_->assert false)
  | Il.CaseE notation -> let name,_ = variant ctx (e.note $ e.at) in let mixop,args=Domain.Mixfix.split notation in
      using_all(List.map lower args)(fun args->ret{typ=result;term=Constructor(Data.constructor_name ctx name mixop,args)})
  | Il.StrE fs -> let name,_=variant ctx (e.note $ e.at) in
      using_all(List.map(fun(_,e)->lower e)fs)(fun args->ret{typ=result;term=Constructor(Data.record_constructor ctx name,args)})
  | Il.DotE(base,atom) -> let name,ts=variant ctx (base.note $ base.at) in
      using(lower base)(fun value->ret(primitive result (Data.field_name ctx name atom)
        (List.map(fun t->lit Unit (Emit_data.render_type(typ ctx t)))ts @ [value])))
  | Il.LenE base -> using(lower base)(fun value->ret(primitive Nat (if is_text ctx value.typ then "String.length" else "List.length")[value]))
  | Il.IdxE(base,index) -> using_all[lower base;lower_index ctx scope index](function[base;index]->
      option_result result(primitive(Option result)(if is_text ctx base.typ then "index_text" else "index_list")[base;index])|_->assert false)
  | Il.SliceE(base,start,count) -> using_all[lower base;lower_index ctx scope start;lower_index ctx scope count](function[base;start;count]->
      option_result result(primitive(Option result)(if is_text ctx base.typ then "slice_text" else "slice_list")[base;start;count])|_->assert false)
  | Il.MemE(element,collection) -> using_all[lower element;lower collection](function[element;collection]->
      ret(primitive Bool ("existsb (equal_value " ^ Emit_data.ops_expr element.typ ^ " " ^ Render.expression element ^ ")")[collection])|_->assert false)
  | Il.MatchE(x,pattern) -> using(lower x)(fun value -> let code = match pattern with
      | Il.ListP `Nil -> "Nat.eqb (List.length " ^ Render.expression value ^ ") 0"
      | Il.ListP `Cons -> "negb (Nat.eqb (List.length " ^ Render.expression value ^ ") 0)"
      | Il.ListP(`Fixed n) -> "Nat.eqb (List.length " ^ Render.expression value ^ ") " ^ string_of_int n
      | Il.OptP kind -> "match " ^ Render.expression value ^ " with None => " ^ (if kind=`None then "true" else "false") ^ " | Some _ => " ^ (if kind=`Some then "true" else "false") ^ " end"
      | Il.CaseP mixop -> let name,_=variant ctx (x.note $ x.at) in let fields=Data.constructor_fields ctx name mixop in
          "match " ^ Render.expression value ^ " with " ^ Data.constructor_name ctx name mixop ^ " " ^ String.concat " " (List.map(fun _->"_")fields)^ " => true" ^ (match (Data.definition ctx name).it with Al.TypD(_,_,{it=Il.VariantT [_];_},_)->" end"|_->" | _ => false end") in
      ret(lit Bool code))
  | Il.CallE(id,ts,args) -> let declaration=Context.find ctx ~namespace:"dec" id.it in
      let arguments=List.map(function {it=Il.ExpA exp;_}->lower exp | {it=Il.DefA f;_}->
          (match Context.find ctx ~namespace:"dec" f.it with
          | Some d -> let signature=Option.get d.signature in
              let types=List.map(typ ctx)signature.argument_types in
              ret{typ=Function_ref{parameters=List.map(fun p->Data.parameter_name ctx p.it)signature.type_parameters;
                    inputs=types;output=typ ctx(List.hd signature.output_types)};term=Function d.generated_name}
          | None -> ret(find_variable scope f.at ("$" ^ f.it)))) args in
      using_all arguments(fun arguments->match declaration with
        | Some d -> {result;node=Invoke{target=d.generated_name;type_arguments=List.map(typ ctx)ts;arguments;result}}
        | None -> let reference=find_variable scope id.at ("$" ^ id.it) in
            (match reference.typ with
            | Function_ref {parameters=[];inputs;_} ->
                let input={typ=(match inputs with []->Unit|[t]->t|ts->Product ts);term=Tuple arguments} in
                {result;node=Invoke{target="#apply";type_arguments=[];arguments=[reference;input];result}}
            | _->fail e.at "CallE" "callback reference has incompatible signature"))
  | Il.UpCastE(target,x) | Il.DownCastE(target,x) ->
      let helper=Casts.request ctx ~source:(x.note $ x.at) ~target in
      using(lower x)(fun value->option_result result(primitive(Option result)helper[value]))
  | Il.SubE(x,_,check) -> using(lower x)(fun value->ret(subcheck ctx (x.note $ x.at) check value))
  | Il.UpdE(base,path,replacement) -> using_all[lower base;lower replacement](function
      | [base;replacement] -> update_path ctx scope base path replacement
      | _->assert false)
  | Il.IterE(inner,(kind,vars)) -> lower_iteration ctx scope result inner kind vars
and lower_index ctx scope expression =
  using(lower_exn ctx scope expression)(fun value ->
    let within_host_range=primitive Bool "Z.leb"
      [primitive Int "Z.of_nat" [value];lit Int "(4611686018427387903)%Z"] in
    {result=value.typ;node=Match(within_host_range,["true",ret value;
      "false",error value.typ "HostConversion" "index exceeds the pinned OCaml int range"])})
and subcheck ctx source check value =
  let raw=(Data.unfold_alias ctx source).it in
  match check with
  | Il.SkipSC -> lit Bool "true"
  | Il.RecurseSC target ->
      let helper=Casts.request ctx ~source ~target in
      let option=primitive(Option(typ ctx target))helper[value] in
      {typ=Bool;term=Match_term(option,["Some _",lit Bool "true";"None",lit Bool "false"])}
  | Il.MixopSC operators ->
      (match raw with
      | Il.VarT(id,_) -> (match (Data.definition ctx id.it).it with
          | Al.TypD(_,_,{it=Il.VariantT cases;_},_) ->
              {typ=Bool;term=Match_term(value,List.map(fun(notation,_,_)->
                let operator,fields=Domain.Mixfix.split notation.it in
                String.concat " " (Data.constructor_name ctx id.it operator::List.map(fun _->"_")fields),
                lit Bool(string_of_bool(List.exists(fun allowed->Data.mixop_key allowed=Data.mixop_key operator)operators)))cases)}
          | _->lit Bool "false")
      | _->lit Bool "false")
  | Il.TupleSC checks -> (match raw with
      | Il.TupleT fields when List.length fields=List.length checks ->
          let names=List.map(fun _->fresh_name())fields in
          let results=List.map2(fun(field,check)name->subcheck ctx field check(lit(typ ctx field)(Render.identifier name))) (List.combine fields checks)names in
          let result=List.fold_right(fun check rest->primitive Bool "andb"[check;rest])results(lit Bool "true") in
          {typ=Bool;term=Match_term(value,[Render.tuple(List.map Render.identifier names),result])}
      | _->lit Bool "false")
  | Il.IterSC(Il.List,check) -> (match raw with
      | Il.IterT(field,Il.List) -> let b={name=fresh_name();typ=typ ctx field} in
          primitive Bool "forallb"[{typ=Unit;term=Lambda([b],subcheck ctx field check(var b))};value]
      | _->lit Bool "false")
  | Il.IterSC(Il.Opt,check) -> (match raw with
      | Il.IterT(field,Il.Opt) -> let name=fresh_name() in
          {typ=Bool;term=Match_term(value,["None",lit Bool "true";
             "Some " ^ Render.identifier name,subcheck ctx field check(lit(typ ctx field)(Render.identifier name))])}
      | _->lit Bool "false")

and update_path ctx scope base path replacement =
  let rec walk path current finish = match path.it with
  | Il.RootP -> finish current (fun replacement -> ret replacement)
  | Il.DotP(parent,field) -> walk parent current (fun parent_value rebuild ->
      let name,ts=variant ctx (parent.note $ parent.at) in
      let field_type=snd(List.find(fun(atom,_)->Data.atom_key atom=Data.atom_key field)(record_fields ctx name ts)) in
      let args=List.map(fun t->lit Unit(Emit_data.render_type(typ ctx t)))ts in
      let selected=primitive (typ ctx field_type) (Data.field_name ctx name field) (args@[parent_value]) in
      finish selected (fun new_value ->
        let values=List.map(fun(atom,field_type)->
          if Data.atom_key atom=Data.atom_key field then new_value
          else primitive (typ ctx field_type) (Data.field_name ctx name atom) (args@[parent_value]))(record_fields ctx name ts) in
        rebuild {typ=parent_value.typ;term=Constructor(Data.record_constructor ctx name,values)}))
  | Il.IdxP(parent,index) -> walk parent current(fun parent_value rebuild ->
      using(lower_index ctx scope index)(fun index_value->
        using(option_result (typ ctx (path.note $ path.at))
          (primitive(Option(typ ctx (path.note $ path.at)))
            (if is_text ctx parent_value.typ then "index_text" else "index_list")[parent_value;index_value]))(fun selected ->
          finish selected(fun new_value ->
            let replacement = if is_text ctx parent_value.typ then new_value else
              lit (List new_value.typ) ("[" ^ Render.expression new_value ^ "]") in
            using(option_result parent_value.typ (primitive(Option parent_value.typ)
              (if is_text ctx parent_value.typ then "splice_text" else "splice_list")
              [parent_value;index_value;lit Nat "1%nat";replacement]))rebuild))))
  | Il.SliceP(parent,start,count) -> walk parent current(fun parent_value rebuild ->
      using_all[lower_index ctx scope start;lower_index ctx scope count](function
        | [start;count] -> using(option_result (typ ctx (path.note $ path.at))
            (primitive(Option(typ ctx (path.note $ path.at)))
              (if is_text ctx parent_value.typ then "slice_text" else "slice_list")[parent_value;start;count]))(fun selected->
              finish selected(fun new_value->using(option_result parent_value.typ
                (primitive(Option parent_value.typ)(if is_text ctx parent_value.typ then "splice_text" else "splice_list")
                  [parent_value;start;count;new_value]))rebuild))
        | _->assert false))
  in walk path base (fun _ rebuild->rebuild replacement)
and lower_iteration ctx scope result inner kind vars =
  if vars=[] then fail inner.at "IterE" "iteration has no variable that determines its extent";
  let keys=List.map(fun(id,_,dims)->source_var_key(id,dims))vars in
  let collections=List.map(fun(id,_,dims)->find_variable scope inner.at(source_var_key(id,dims@[kind])))vars in
  let elements=List.map(fun value->match unfold_type ctx value.typ with List t|Option t->t|_->fail inner.at "IterE" "iteration variable has wrong container")collections in
  let locals=List.map2(fun name typ->{name;typ})keys elements in
  let scope'=locals@scope in
  let inner_action=lower_exn ctx scope' inner in
  let pattern_names=List.map(fun _->fresh_name())vars in
  let pattern_values=List.map2(fun name typ->lit typ(Render.identifier name))pattern_names elements in
  let with_locals action=List.fold_right2(fun b value action->local b value action)locals pattern_values action in
  match kind with
  | Il.List ->
      let zipped=match collections with
        | first::rest -> fst(List.fold_left(fun(acc,types) value->
            let element=match unfold_type ctx value.typ with List t->t|_->assert false in
            let types=types@[element] in primitive(List(Product types)) "combine" [acc;value],types)
            (first,[List.hd elements])rest)
        | []->assert false in
      let row={name=fresh_name();typ=Product elements} in
      let body={result=inner_action.result;node=Match(var row,[Render.tuple(List.map Render.identifier pattern_names),with_locals inner_action])} in
      let action={result;node=Traverse(row,zipped,body)} in
      let first=List.hd collections in
      List.fold_right(fun x rest ->
        let condition=primitive Bool "Nat.eqb"[primitive Nat "List.length"[first];primitive Nat "List.length"[x]] in
        {result;node=Match(condition,["true",rest;"false",error result "StructureError" "iteration lengths differ"])})(List.tl collections)action
  | Il.Opt ->
      let all_some=Render.tuple(List.map(fun n->"Some " ^ Render.identifier n)pattern_names) in
      let all_none=Render.tuple(List.map(fun _->"None")vars) in
      let present=with_locals(using inner_action(fun value->ret(primitive result "Some"[value]))) in
      {result;node=Match({typ=Product(List.map(fun e->e.typ)collections);term=Tuple collections},
        [all_none,ret(lit result "None");all_some,present] @
        (if List.length vars>1 then ["_",error result "StructureError" "iteration option shapes differ"] else []))}

let lower ctx scope e = try counter:=0;Ok(lower_exn ctx scope e) with Unsupported d | Data.Unsupported d -> Error[d]
