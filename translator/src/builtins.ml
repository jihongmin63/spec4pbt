open Util.Source
open Lang
open Coq_ir
module E = Lower_expr

exception Unsupported of diagnostic
let fail d reason = raise (Unsupported {stage="builtin";location=d.Context.location;
  construct=d.kind ^ ":" ^ d.source_name;reason})

(* These are source signatures, before alias expansion.  Parameters are alpha
   normalized by position so their spelling cannot change dispatch. *)
type shape = B | N | I | T | P of int | L of shape | O of shape
           | Tuple of shape list | Name of string * shape list
type entry = { name:string; parameters:int; inputs:shape list; output:shape;
               unit_name:string; needs_ops:bool; failures:string list }
let entry ?(parameters=0) ?(ops=false) ?(failures=[]) unit_name name inputs output =
  {name;parameters;inputs;output;unit_name;needs_ops=ops;failures}
let entries =
  let p=P 0 and q=P 1 in
  let set=Name("set",[P 0]) and map=Name("map",[P 0;P 1]) and bits=Name("bits",[]) in
  [entry "nats" "sum_nat" [L N] N;
   entry ~failures:["Unmatch: empty input"] "nats" "max_nat" [L N] N;
   entry ~failures:["Unmatch: empty input"] "nats" "min_nat" [L N] N;
   entry "ints" "sum_int" [L I] I;entry "ints" "max_int" [L I] I;entry "ints" "min_int" [L I] I;
   entry ~failures:["HostConversion: malformed Bigint string"] "texts" "text_to_int" [T] I;
   entry "texts" "int_to_text" [I] T;
   entry ~failures:["HostConversion: separator is not one byte"] "texts" "split_text" [T;T] (L T);
   entry ~failures:["HostConversion: missing prefix"] "texts" "strip_prefix" [T;T] T;
   entry ~failures:["HostConversion: missing suffix"] "texts" "strip_suffix" [T;T] T;
   entry "texts" "strip_all_whitespace" [T] T;
   entry ~parameters:1 "lists" "rev_" [L p] (L p);
   entry ~parameters:1 "lists" "concat_" [L(L p)] (L p);
   entry ~parameters:1 ~failures:["HostConversion: nat exceeds OCaml int range"] "lists" "partition_" [L p;N] (Tuple[L p;L p]);
   entry ~parameters:2 ~ops:true "lists" "assoc_" [p;L(Tuple[p;q])] (O q);
   entry ~parameters:1 "lists" "sort_" [L(Tuple[N;p])] (L(Tuple[N;p]));
   entry ~parameters:1 ~ops:true "lists" "distinct_" [L p] B;
   entry ~parameters:1 ~ops:true "sets" "intersect_set" [set;set] set;
   entry ~parameters:1 ~ops:true "sets" "union_set" [set;set] set;
   entry ~parameters:1 ~ops:true "sets" "unions_set" [L set] set;
   entry ~parameters:1 ~ops:true "sets" "diff_set" [set;set] set;
   entry ~parameters:1 ~ops:true "sets" "sub_set" [set;set] B;
   entry ~parameters:1 ~ops:true "sets" "eq_set" [set;set] B;
   entry ~parameters:2 ~ops:true "maps" "find_map" [map;p] (O q);
   entry ~parameters:2 ~ops:true "maps" "find_maps" [L map;p] (O q);
   entry ~parameters:2 ~ops:true "maps" "add_map" [map;p;q] map;
   entry ~parameters:2 ~ops:true ~failures:["HostConversion: key/value lengths differ"] "maps" "adds_map" [map;L p;L q] map;
   entry ~parameters:2 ~ops:true "maps" "update_map" [map;p;q] map;
   entry ~parameters:1 ~ops:true ~failures:["HostConversion: P4 unparse fails"] "interface" "print_" [p] T;
   entry "fresh" "fresh_typeId" [] (Name("typeId",[]));
   entry ~failures:["Unmatch: width > 2048"] "numerics" "bitstr_to_int" [I;I] I;
   entry ~failures:["Unmatch: width > 2048"] "numerics" "int_to_bitstr" [I;I] I;
   entry "numerics" "bits_to_int_unsigned" [bits] I;
   entry ~failures:["Unmatch: empty bits"] "numerics" "bits_to_int_signed" [bits] I;
   entry ~failures:["Unmatch: width > 2048"] "numerics" "int_to_bits_unsigned" [N;I] bits;
   entry ~failures:["Unmatch: width > 2048"] "numerics" "int_to_bits_signed" [N;I] bits;
   entry "numerics" "pow2" [N] I;
   entry ~failures:["Unmatch: offset > 2048"] "numerics" "shl" [I;I] I;
   entry ~failures:["Unmatch: offset > 2048"] "numerics" "shr" [I;I] I;
   entry ~failures:["Unmatch: offset > 2048"] "numerics" "shr_arith" [I;I;I] I;
   entry "numerics" "bneg" [I] I;
   entry "numerics" "band" [I;I] I;entry "numerics" "bxor" [I;I] I;entry "numerics" "bor" [I;I] I;
   entry ~failures:["HostConversion: negative or non-host low index"] "numerics" "bitacc" [I;I;I] I;
   entry ~failures:["HostConversion: negative or non-host low index"] "numerics" "bitacc_replace" [I;I;I;I] I]

let rec shape parameters t = match t.it with
  | Il.BoolT -> B | Il.NumT `NatT -> N | Il.NumT `IntT -> I | Il.TextT -> T
  | Il.IterT(t,Il.List) -> L(shape parameters t) | Il.IterT(t,Il.Opt) -> O(shape parameters t)
  | Il.TupleT ts -> Tuple(List.map(shape parameters)ts)
  | Il.VarT(id,ts) -> (match List.find_index ((=) id.it) parameters with
      | Some i when ts=[] -> P i
      | _ -> Name(id.it,List.map(shape parameters)ts))
  | Il.FuncT _ -> Name("#function",[])

let validate ctx (d:Context.declaration) =
  if d.kind<>"BuiltinDecD" || d.namespace<>"dec" then fail d "dispatch requires a builtin declaration in the dec namespace";
  (match d.definition.it with Al.BuiltinDecD _ -> () | _ -> fail d "declaration metadata does not match BuiltinDecD AST");
  if ctx.Context.profile.name<>"p4" &&
     not(ctx.profile.name="wasm" && List.mem d.source_name ["union_set";"diff_set"])
  then fail d ("builtin profile/name is unsupported: " ^ ctx.profile.name ^ "/" ^ d.source_name);
  let implementation=match List.find_opt(fun e->e.name=d.source_name)entries with
    | Some e->e | None->fail d "no pinned P4 builtin implementation" in
  let signature=match d.signature with Some s->s | None->fail d "builtin has no indexed signature" in
  let parameters=List.map(fun p->p.it)signature.type_parameters in
  let expected_inputs=List.init(List.length implementation.inputs)Fun.id in
  if List.length parameters<>implementation.parameters ||
     List.map(shape parameters)signature.argument_types<>implementation.inputs ||
     List.map(shape parameters)signature.output_types<>[implementation.output] ||
     signature.input_positions<>expected_inputs || signature.output_positions<>[List.length expected_inputs] ||
     signature.input_hint<>None || List.length signature.parameters<>List.length expected_inputs ||
     not(List.for_all(fun p->match p.it with Il.ExpP _->true | _->false)signature.parameters)
  then fail d "builtin signature differs from the pinned P4 implementation contract";
  implementation,signature

(* map<K,V> unfolds to set<pair<K,V>>.  Resolve the actual constructor metadata,
   rather than manufacturing constructor names or treating wrappers as lists. *)
let wrapper ctx typ =
  let expanded=Data.unfold_alias ctx typ in
  match expanded.it with
  | Il.VarT(id,ts) when id.it="set" || id.it="pair" ->
      (match (Data.definition ctx id.it).it with
       | Al.TypD(_,ps,{it=Il.VariantT[(notation,_,_)];_},_) when List.length ps=List.length ts ->
           let mixop,fields=Domain.Mixfix.split notation.it in
           let fields=List.map(Data.substitute(List.map2(fun p t->p.it,t)ps ts))fields in
           Some(Data.constructor_name ctx id.it mixop,ts,fields)
       | _ -> Data.fail typ.at "builtin-wrapper" "set/pair must have one constructor with matching parameters")
  | _ -> None
let rec native_type ctx typ = match wrapper ctx typ with
  | Some(_,_,[field]) -> native_type ctx field
  | Some(_,_,fields) -> Product(List.map(native_type ctx)fields)
  | None -> let expanded=Data.unfold_alias ctx typ in match expanded.it with
      | Il.IterT(t,Il.List)->List(native_type ctx t)
      | Il.IterT(t,Il.Opt)->Option(native_type ctx t)
      | Il.TupleT []->Unit | Il.TupleT ts->Product(List.map(native_type ctx)ts)
      | _->E.typ ctx expanded
let pattern constructor parameters names =
  "@" ^ constructor ^ " " ^ String.concat " " (List.map(fun _->"_")parameters @ List.map Render.identifier names)
let lambda b body = {typ=Unit;term=Lambda([b],body)}
let rec unwrap ctx typ value = match wrapper ctx typ with
  | Some(constructor,parameters,fields) ->
      let names=List.map(fun _->E.fresh_name())fields in
      let values=List.map2(fun name field->unwrap ctx field (E.lit(E.typ ctx field)(Render.identifier name)))names fields in
      let body=match values with [x]->x | xs->{typ=native_type ctx typ;term=Coq_ir.Tuple xs} in
      {typ=native_type ctx typ;term=Match_term(value,[pattern constructor parameters names,body])}
  | None -> let expanded=Data.unfold_alias ctx typ in match expanded.it with
      | Il.IterT(t,Il.List) -> let b={name=E.fresh_name();typ=E.typ ctx t} in
          E.primitive(native_type ctx typ) "map" [lambda b (unwrap ctx t (E.var b));value]
      | Il.IterT(t,Il.Opt) -> let b={name=E.fresh_name();typ=E.typ ctx t} in
          E.primitive(native_type ctx typ) "option_map" [lambda b (unwrap ctx t (E.var b));value]
      | Il.TupleT ts when ts<>[] ->
          let names=List.map(fun _->E.fresh_name())ts in
          {typ=native_type ctx typ;term=Match_term(value,[Render.tuple(List.map Render.identifier names),
            {typ=native_type ctx typ;term=Coq_ir.Tuple(List.map2(fun name t->unwrap ctx t(E.lit(E.typ ctx t)(Render.identifier name)))names ts)}])}
      | _ -> {value with typ=native_type ctx typ}
let rec wrap ctx typ value = match wrapper ctx typ with
  | Some(constructor,parameters,fields) ->
      let construct values = E.primitive(E.typ ctx typ) ("@"^constructor)
        (List.map(fun t->E.lit Unit(Emit_data.render_type(E.typ ctx t)))parameters @ List.map2(wrap ctx)fields values) in
      (match fields with
       | [field] -> construct [{value with typ=native_type ctx field}]
       | _ -> let names=List.map(fun _->E.fresh_name())fields in
           {typ=E.typ ctx typ;term=Match_term(value,[Render.tuple(List.map Render.identifier names),
             construct(List.map2(fun name field->E.lit(native_type ctx field)(Render.identifier name))names fields)])})
  | None -> let expanded=Data.unfold_alias ctx typ in match expanded.it with
      | Il.IterT(t,Il.List) -> let b={name=E.fresh_name();typ=native_type ctx t} in
          E.primitive(E.typ ctx typ) "map" [lambda b (wrap ctx t(E.var b));value]
      | Il.IterT(t,Il.Opt) -> let b={name=E.fresh_name();typ=native_type ctx t} in
          E.primitive(E.typ ctx typ) "option_map" [lambda b (wrap ctx t(E.var b));value]
      | Il.TupleT ts when ts<>[] ->
          let names=List.map(fun _->E.fresh_name())ts in
          {typ=E.typ ctx typ;term=Match_term(value,[Render.tuple(List.map Render.identifier names),
            {typ=E.typ ctx typ;term=Coq_ir.Tuple(List.map2(fun name t->wrap ctx t(E.lit(native_type ctx t)(Render.identifier name)))names ts)}])}
      | _ -> {value with typ=E.typ ctx typ}

let lower_shared_exn ctx d (arguments:binding list) =
  let implementation,signature=validate ctx d in
  if List.map(fun(b:binding)->b.typ)arguments<>List.map(E.typ ctx)signature.argument_types
  then fail d "builtin input bindings differ from the validated source argument types";
  let inputs=List.map2(fun t b->unwrap ctx t(E.var b))signature.argument_types arguments in
  let inputs=match implementation.name,inputs with
    | ("pow2"|"int_to_bits_unsigned"|"int_to_bits_signed"),first::rest -> E.primitive Int "Z.of_nat" [first] :: rest
    | _ -> inputs in
  let parameters=List.map(fun p->Type_parameter(Data.parameter_name ctx p.it))signature.type_parameters in
  let helper="(@P4." ^ implementation.name ^ " Call" ^ String.concat "" (List.map(fun t->" " ^ Emit_data.render_type t)parameters) ^ ")" in
  let inputs=if implementation.needs_ops then E.lit Unit(Emit_data.ops_expr(List.hd parameters))::inputs else inputs in
  let output=List.hd signature.output_types in
  let action={result=native_type ctx output;node=Primitive_action(helper,inputs)} in
  E.using action (fun result->E.ret(wrap ctx output result))

let lower_exn ctx d arguments =
  if ctx.Context.profile.name="wasm" && not(List.mem d.Context.source_name ["union_set";"diff_set"])
  then (try Wasm_bindings.lower_exn ctx d arguments with Wasm_bindings.Unsupported d -> raise(Unsupported d))
  else lower_shared_exn ctx d arguments

let lower ctx d arguments = try Ok(lower_exn ctx d arguments)
  with Unsupported d | Data.Unsupported d | E.Unsupported d -> Error[d]

let shared_bindings ctx =
  `List(List.filter_map(fun(d:Context.declaration)->if d.kind<>"BuiltinDecD" ||
      (ctx.Context.profile.name="wasm" && not(List.mem d.source_name ["union_set";"diff_set"])) then None else
    let implementation,signature=validate ctx d in
    Some(`Assoc["profile",`String ctx.Context.profile.name;"declaration_kind",`String d.kind;
      "source_name",`String d.source_name;"generated_name",`String d.generated_name;
      "signature",Context.signature_to_json signature;
      "runtime_helper",`String("P4."^implementation.name);
      "runtime_source",`String "translator/coq/Builtins/P4.v";
      "native_source",`String(if implementation.unit_name="interface" then "p4spec/lib/interface/interface.ml" else
        "p4spec/lib/interface/builtin/"^implementation.unit_name^".ml");
      "failure_policy",`List(List.map(fun s->`String s)implementation.failures);
      "success_policy",`String(if implementation.name="fresh_typeId" then "consume fresh state and return FRESH__ counter text" else "return the concrete pinned-source result");
      "value_operations",`Bool implementation.needs_ops;
      "wrapper_conversion",`String "source set/pair constructors; map alias set<pair>; native lists and products" ]))ctx.Context.declarations)

let bindings ctx =
  let shared = match shared_bindings ctx with `List xs->xs|_->assert false in
  `List (shared @ (if ctx.Context.profile.name="wasm" then Wasm_bindings.bindings ctx else []))
