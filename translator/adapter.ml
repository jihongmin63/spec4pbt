open Common.Source
open Lang.Il
module I = Ir

let typ = function
  | BoolT -> I.Bool | NumT `NatT -> I.Nat | NumT `IntT -> I.Int | TextT -> I.Text
  | VarT {synid; targs = []} -> I.Named synid.it
  | t -> I.unsupported ("type: " ^ Print.string_of_typ (t $ no_region))
let atom a = Lang.Xl.Atom.to_string a.it

let translate (source : spec) =
  let variants = List.filter_map (fun d -> match d.it with
    | TypD {synid; deftyp = {it = VariantT cases; _}; _} -> Some (synid.it, cases)
    | _ -> None) source in
  let constructor t notation =
    match t with
    | VarT {synid; targs = []} ->
      let cases = try List.assoc synid.it variants with Not_found -> I.unsupported "constructor type" in
      let rec find i = function
        | [] -> I.unsupported "unknown variant constructor"
        | c :: cs -> if Mixfix.eq_mixop c.notation.it notation then
            (synid.it, i, Mixfix.arity c.notation.it) else find (i+1) cs in
      find 0 cases
    | _ -> I.unsupported "constructor on non-variant"
  in
  let rec expr (e : exp) : I.expr =
    let node = match e.it with
    | VarE id -> I.Var id.it
    | BoolE b -> I.Literal (string_of_bool b)
    | NumE n -> I.Literal (Bigint.to_string (Lang.Xl.Num.to_int n))
    | TextE s -> I.Literal (Yojson.Basic.to_string (`String s))
    | UnE (`PlusOp, _, e) -> (expr e).node
    | UnE (`MinusOp, _, e) ->
      let value = expr e in
      let value = if value.typ = I.Nat then {I.typ = I.Int; node = I.NatToInt value} else value in
      I.Unary ("-", value)
    | UnE (`NotOp, _, e) -> I.Unary ("!", expr e)
    | BinE (op, _, a, b) ->
      let op = match op with
        | `AddOp -> "+" | `SubOp when e.note = NumT `IntT -> "-"
        | `MulOp -> "*" | `AndOp -> "&&" | `OrOp -> "||"
        | _ -> I.unsupported "partial or unsupported binary operation (including nat subtraction, division, modulo, power)" in
      I.Binary (op, expr a, expr b)
    | CmpE (op, _, a, b) ->
      let op = match op with `EqOp -> "=" | `NeOp -> "≠" | `LtOp -> "<" | `GtOp -> ">" | `LeOp -> "≤" | `GeOp -> "≥" in
      I.Compare (op, expr a, expr b)
    | CaseE notation -> let name, index, _ = constructor e.note notation in
      I.Constructor (name, index, List.map expr (Mixfix.args notation))
    | StrE fields -> I.Record (List.map (fun (a,e) -> atom a, expr e) fields)
    | DotE (e,a) -> I.Field (expr e, atom a)
    | MatchE (e, CaseP notation) -> let name, index, arity = constructor e.note notation in
      let value = expr e in
      if List.length (List.assoc name variants) = 1 then I.Literal "true"
      else I.IsConstructor (value, index, arity)
    | UpCastE ({it = NumT `IntT; _}, a) when a.note = NumT `NatT ->
      let value = expr a in
      if value.typ = I.Int then value.node else I.NatToInt value
    | SubE _ -> I.unsupported "subtype membership checks"
    | _ -> I.unsupported ("expression: " ^ Print.string_of_exp e) in
    let result_type = match e.it with UnE (`MinusOp, _, _) -> I.Int | _ -> typ e.note in
    {I.typ = result_type; node}
  in
  let relation_types = List.filter_map (fun d -> match d.it with
    | RelD {relid; reltyp; _} -> Some (relid.it, reltyp.it) | _ -> None) source in
  let rule rt (r : rule) =
    let ins, outs = Mode.partition rt (Mixfix.args r.it.concl) in
    let steps = List.filter_map (fun (p : prem) -> match p.it with
      | LetPr (a,b) -> Some (I.Bind (expr a, expr b))
      | IfPr {cond; _} -> Some (I.Guard (expr cond))
      | RelPr {relid; notexp} ->
        let rt = List.assoc relid.it relation_types in
        let ins, outs = Mode.partition rt (Mixfix.args notexp) in
        Some (I.Call (relid.it, List.map expr ins, List.map expr outs))
      | ElsePr -> None
      | _ -> I.unsupported "premise (assertions, iterations, debugging are unsupported)") r.it.prems in
    let fallback = match List.rev r.it.prems with {it = ElsePr; _} :: _ -> true | _ -> false in
    if List.exists (fun (p : prem) -> p.it = ElsePr) r.it.prems && not fallback then
      I.unsupported "otherwise must be the final premise";
    {I.inputs = List.map expr ins; outputs = List.map expr outs; steps; fallback}
  in
  let types = List.filter_map (fun d -> match d.it with
    | TypD {synid; tparams = []; deftyp} ->
      let td = match deftyp.it with
        | StructT fs -> I.RecordType (List.map (fun (a,t) -> atom a, typ t.it) fs)
        | VariantT cs -> I.VariantType (List.map (fun c -> List.map (fun t -> typ t.it) (Mixfix.args c.notation.it)) cs)
        | PlainT t -> I.Alias (typ t.it) in
      Some (synid.it, td)
    | TypD _ -> I.unsupported "polymorphic type"
    | RelD _ -> None
    | _ -> I.unsupported "function or builtin definition") source in
  let relations = List.filter_map (fun d -> match d.it with
    | RelD {relid; reltyp; rules} ->
      let slots = List.map (function Mode.In t -> true, typ t.it | Mode.Out t -> false, typ t.it) (Mixfix.args reltyp.it) in
      let rules = List.map (rule reltyp.it) rules in
      let fallback, ordinary = List.partition (fun r -> r.I.fallback) rules in
      Some {I.name = relid.it; slots; rules = ordinary @ fallback}
    | _ -> None) source in
  {I.types; relations}
