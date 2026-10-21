(** Typed property frontend: the official parser and elaborator own syntax/types. *)
open Util.Source
open Lang
module S = Lang.Il
let obj x = `Assoc x
let str x = `String x
let arr f x = `List (List.map f x)
let fail at message = raise (Failure (Format.asprintf "%s:%d:%d: %s" at.left.file at.left.line at.left.column message))
let loc at = obj ["file",str at.left.file; "line",`Int at.left.line; "column",`Int at.left.column]
let quote s = "«" ^ s ^ "»"
(* Same structural keys as observation metadata; never parse printed types. *)
let rec type_key (t:S.typ) = match t.it with
  | BoolT -> "bool" | NumT `NatT -> "nat" | NumT `IntT -> "int" | TextT -> "text"
  | VarT (id, []) -> id.it
  | VarT (id, args) -> id.it ^ "<" ^ String.concat "," (List.map (fun (x:S.targ) -> type_key (x.it $ x.at)) args) ^ ">"
  | IterT (t, List) -> "[" ^ type_key t ^ "]"
  | IterT (t, Opt) -> "?" ^ type_key t
  | TupleT ts -> "(" ^ String.concat "," (List.map type_key ts) ^ ")"
  | _ -> fail t.at "unsupported property type"
let rec typ (t:S.typ) =
  let lean = match t.it with
  | BoolT -> "Bool" | NumT `NatT -> "Nat" | NumT `IntT -> "Int" | TextT -> "String"
  | VarT (id, args) -> "(SpecTec." ^ quote id.it ^ String.concat "" (List.map (fun (x:S.targ) -> " " ^ lean_typ (x.it $ x.at)) args) ^ ")"
  | IterT (t, List) -> "(List " ^ lean_typ t ^ ")"
  | IterT (t, Opt) -> "(Option " ^ lean_typ t ^ ")"
  | TupleT ts -> "(" ^ String.concat " × " (List.map lean_typ ts) ^ ")"
  | _ -> fail t.at "unsupported property type" in
  obj ["lean",str lean; "key",str (type_key t); "source",str (S.Print.string_of_typ t)]
and lean_typ t = match typ t with `Assoc xs -> (match List.assoc "lean" xs with `String x -> x | _ -> assert false) | _ -> assert false
let rec exp (x:S.exp) =
  let base = ["type",typ (x.note $ x.at); "location",loc x.at] in
  let fields = match x.it with
  | VarE id -> ["kind",str "variable"; "name",str id.it]
  | BoolE b -> ["kind",str "bool"; "value",`Bool b]
  | NumE n -> ["kind",str "number"; "value",str (Bigint.to_string (Xl.Num.to_int n))]
  | TextE t -> ["kind",str "text"; "value",str t]
  | StrE fs -> ["kind",str "record"; "fields",obj (List.map (fun ((a:S.atom),e) -> Domain.Atom.string_of_atom a.it,exp e) fs)]
  | TupleE xs -> ["kind",str "tuple"; "items",arr exp xs]
  | ListE xs -> ["kind",str "list"; "items",arr exp xs]
  | OptE xo -> ["kind",str "option"; "items",arr exp (Option.to_list xo)]
  | DotE (e,a) -> ["kind",str "field"; "base",exp e; "field",str (Domain.Atom.string_of_atom a.it)]
  | IdxE (e,i) -> ["kind",str "index"; "base",exp e; "index",exp i]
  | SliceE (e,i,n) -> ["kind",str "slice"; "base",exp e; "index",exp i; "length",exp n]
  | UpCastE (_,e) -> ["kind",str "cast"; "value",exp e]
  | DownCastE (_,e) -> ["kind",str "downcast"; "value",exp e]
  | SubE (e,_,_) -> ["kind",str "subtype"; "value",exp e]
  | MatchE (e,p) -> ["kind",str "match"; "value",exp e; "pattern",str (S.Print.string_of_pattern p)]
  | UnE (op,_,e) -> ["kind",str "unary"; "operator",str (S.Print.string_of_unop op); "value",exp e]
  | BinE (op,_,a,b) -> ["kind",str "binary"; "operator",str (S.Print.string_of_binop op); "left",exp a; "right",exp b]
  | CmpE (op,_,a,b) -> ["kind",str "compare"; "operator",str (S.Print.string_of_cmpop op); "left",exp a; "right",exp b]
  | CallE (id,_,args) -> ["kind",str "call"; "name",str id.it; "arguments",arr (fun (a:S.arg) -> match a.it with ExpA x -> exp x | _ -> fail a.at "function-valued property argument") args]
  | LenE e -> ["kind",str "length"; "value",exp e]
  | ConsE (a,b) -> ["kind",str "cons"; "left",exp a; "right",exp b]
  | CatE (a,b) -> ["kind",str "concat"; "left",exp a; "right",exp b]
  | MemE (a,b) -> ["kind",str "member"; "left",exp a; "right",exp b]
  | IterE (e,_) -> ["kind",str "iterate"; "value",exp e]
  | CaseE ne -> ["kind",str "constructor"; "notation",str (Domain.Mixfix.to_string ne); "arguments",arr exp (Domain.Mixfix.args ne)]
  | _ -> fail x.at ("unsupported property expression: " ^ S.Print.string_of_exp x) in
  obj (base @ fields)
let prem (p:S.prem) =
  match p.it with
  | RulePr (id,ne,inputs) -> obj ["kind",str "relation"; "relation",str id.it; "inputs",arr (fun i -> `Int i) inputs; "arguments",arr exp (Domain.Mixfix.args ne); "location",loc p.at]
  | IfHoldPr (id,ne) -> let args=Domain.Mixfix.args ne in obj ["kind",str "relation";"relation",str id.it;"inputs",arr (fun i -> `Int i) (List.init (List.length args) Fun.id);"arguments",arr exp args;"location",loc p.at]
  | IfPr x -> obj ["kind",str "guard";"expression",exp x;"location",loc p.at]
  | LetPr (target,value) -> obj ["kind",str "let";"target",exp target;"value",exp value;"location",loc p.at]
  | _ -> fail p.at "unsupported property premise"
let binding origin ((id:S.id),t) = obj ["name",str id.it;"type",typ t;
  "producer",str origin;"location",loc id.at]
let property spec ((id:S.id),inputs,goal,conditions as clause) =
  let blocks, goal_nodes = match Pass.algo_property spec clause with
    | Ok x -> x | Error d -> failwith (Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain (Diagnostic.Report.singleton d)) in
  let condition_blocks = List.mapi (fun index nodes ->
    let source = List.nth conditions index in
    let kind = match source.it with RulePr _ | IfHoldPr _ -> "relation" | _ -> "guard" in
    Property_al.block prem binding ("condition." ^ string_of_int index) kind nodes) blocks in
  let goal_kind = match goal.it with RulePr _ | IfHoldPr _ -> "relation" | _ -> "guard" in
  obj ["name",str id.it;"location",loc id.at;"inputs",arr (fun ((id:S.id),t)->obj["name",str id.it;"type",typ t;"location",loc id.at]) inputs;"goal",prem goal;"conditions",arr prem conditions;
       "condition_blocks",`List condition_blocks;"goal_block",Property_al.block prem binding "goal" goal_kind goal_nodes]
let read path = let ic=open_in path in Fun.protect ~finally:(fun()->close_in ic) (fun()->really_input_string ic (in_channel_length ic))
let report d = Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain (Diagnostic.Report.singleton d)
let () = try
  let specs=ref [] and path=ref "" in
  Arg.parse ["--spec",Arg.String(fun x->specs:= !specs@[x]),"SpecTec source";"--property",Arg.Set_string path,"property file"] (fun _ -> fail no_region "unexpected argument") "property_cli --spec FILE --property FILE";
  if !specs=[] || !path="" then fail no_region "--spec and --property are required";
  let spec = match Pass.parse !specs with Ok x -> x | Error d -> failwith(report d) in
  let lex=Lexing.from_string (read !path) in
  lex.lex_curr_p <- {lex.lex_curr_p with pos_fname= !path};
  let props = try Frontend.Parser.properties Frontend.Lexer.token lex with Frontend.Parser.Error -> fail (Frontend.Lexer.region lex) "invalid property clause syntax" in
  let names=Hashtbl.create 8 in
  let spec_il = match Pass.elab !specs with Ok x -> x | Error d -> failwith(report d) in
  let props=List.map (fun ((id:El.id),_,_,_ as p)->if Hashtbl.mem names id.it then fail id.at "duplicate property name";Hashtbl.add names id.it (); property spec_il (match Pass.elab_property spec p with Ok p -> p | Error d -> failwith(report d))) props in
  print_endline (Yojson.Basic.to_string(obj ["schema_version",`Int 2;"engine",str "spectec-al";"properties",`List props]))
with
| Failure s | Sys_error s -> prerr_endline s; exit 1
| Frontend.Error.ParseError d -> prerr_endline (report d); exit 1
