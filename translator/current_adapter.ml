(** Current SpecTecX IL to the vendored backend's normalized IL boundary.

    SpecTecX performs binding analysis during elaboration.  Preserve those
    premises and only reconstruct the metadata that the older backend expects;
    do not run the donor's frontend or its separate AL binding pass. *)
open Common.Source
module C = Lang.Il
module S = Lean_backend.Lang.Il
module M = Lean_backend.Domain.Mixfix
module A = Lean_backend.Domain.Atom
module Names = Set.Make (String)
module Bindings = Set.Make (struct
  type t = string * C.iter list
  let compare = Stdlib.compare
end)

let unsupported = Lean_backend.Translator.unsupported

let atom (a : C.atom) : S.atom =
  A.atom_of_string (Lang.Xl.Atom.unparse a.it) $ a.at

let mixfix f notation =
  M.Seq (List.map (function
    | C.Mixfix.Arg x -> M.Arg (f x)
    | C.Mixfix.Atom a -> M.Atom (atom a)) notation)

let iter = function C.Opt -> S.Opt | C.List -> S.List

let rec typ (t : C.typ) : S.typ = typ_node t.at t.it $ t.at
and typ_node at = function
  | C.BoolT -> S.BoolT
  | C.NumT n -> S.NumT n
  | C.TextT -> S.TextT
  | C.VarT {synid; targs} -> S.VarT (synid, List.map typ targs)
  | C.TupleT ts -> S.TupleT (List.map typ ts)
  | C.IterT {typ = t; iter = i} -> S.IterT (typ t, iter i)
  | C.FuncT -> unsupported at "function value with an erased signature"

let var (v : C.var) : S.var = v.varid, typ v.typ, List.map iter v.iters
let nottyp (t : C.nottyp) : S.nottyp = mixfix typ t.it $ t.at

let rec param (p : C.param) : S.param =
  (match p.it with
  | C.ExpP t -> S.ExpP (typ t)
  | C.DefP {defid; tparams; params; typ = t} ->
      S.DefP (defid, tparams, List.map param params, typ t)) $ p.at

(* Keep runtime subtype checks precise.  The donor optimization only tests a
   variant's tag when its payload is already constrained by the source type. *)
type type_definition = C.tparam list * C.deftyp

type context = {
  ordered : bool;
  types : (string, type_definition) Hashtbl.t;
  relations : (string, C.reltyp) Hashtbl.t;
}

let rec substitute theta (t : C.typ) : C.typ =
  match t.it with
  | C.VarT {synid; targs = []} when List.mem_assoc synid.it theta ->
      List.assoc synid.it theta
  | C.VarT {synid; targs} ->
      C.VarT {synid; targs = List.map (substitute theta) targs} $ t.at
  | C.TupleT ts -> C.TupleT (List.map (substitute theta) ts) $ t.at
  | C.IterT {typ; iter} -> C.IterT {typ = substitute theta typ; iter} $ t.at
  | _ -> t

let definition ctx (t : C.typ) = match t.it with
  | C.VarT {synid; targs} ->
      (match Hashtbl.find_opt ctx.types synid.it with
      | Some (parameters, body) ->
          if List.length parameters <> List.length targs then
            unsupported t.at ("type argument count for " ^ synid.it);
          Some (List.map2 (fun p a -> p.it, a) parameters targs, body)
      | None -> None)
  | _ -> None

let rec expand ctx seen (t : C.typ) = match t.it, definition ctx t with
  | C.VarT {synid; _}, Some (theta, {it = C.PlainT body; _}) ->
      if Names.mem synid.it seen then
        unsupported t.at ("cyclic type alias " ^ synid.it);
      expand ctx (Names.add synid.it seen) (substitute theta body)
  | _ -> t

let expand ctx = expand ctx Names.empty

let variant ctx t = match definition ctx t with
  | Some (theta, {it = C.VariantT cases; _}) ->
      Some (List.map (fun (c : C.typcase) ->
        C.Mixfix.map (substitute theta) c.notation.it) cases)
  | _ -> None

let rec subtype ctx (left : C.typ) (right : C.typ) =
  let left, right = expand ctx left, expand ctx right in
  C.Eq.eq_typ left right ||
  match left.it, right.it with
  | C.NumT `NatT, C.NumT `IntT -> true
  | C.TupleT ls, C.TupleT rs ->
      List.length ls = List.length rs && List.for_all2 (subtype ctx) ls rs
  | C.IterT {typ = l; iter = li}, C.IterT {typ = r; iter = ri} when li = ri ->
      subtype ctx l r
  | C.VarT _, C.VarT _ ->
      (match variant ctx left, variant ctx right with
      | Some ls, Some rs ->
          List.for_all (fun l -> List.exists (fun r ->
            C.Mixfix.eq_mixop l r &&
            let la, ra = C.Mixfix.args l, C.Mixfix.args r in
            List.length la = List.length ra && List.for_all2 (fun l r ->
              C.Eq.eq_typ (expand ctx l) (expand ctx r)) la ra) rs) ls
      | _ -> false)
  | _ -> false

let rec subcheck ctx source target =
  if subtype ctx source target then S.SkipSC else
  let source', target' = expand ctx source, expand ctx target in
  match source'.it, target'.it with
  | C.TupleT ss, C.TupleT ts when List.length ss = List.length ts ->
      S.TupleSC (List.map2 (subcheck ctx) ss ts)
  | C.IterT {typ = s; iter = si}, C.IterT {typ = t; iter = ti} when si = ti ->
      S.IterSC (iter si, subcheck ctx s t)
  | C.VarT _, C.VarT _ when subtype ctx target' source' ->
      (match variant ctx target' with
      | Some cases -> S.MixopSC (List.map (mixfix (fun _ -> ())) cases)
      | None -> S.RecurseSC (typ target))
  | _ -> S.RecurseSC (typ target)

(* Current elaboration can retain a Nat annotation on unary minus even though
   Num.un returns an Int. Do not use that annotation to erase a subtype test. *)
let rec runtime_type ctx (e : C.exp) : C.typ =
  match e.it with
  | C.UnE (`MinusOp, _, _) -> C.NumT `IntT $ e.at
  | C.UnE (`PlusOp, _, inner) -> runtime_type ctx inner
  | C.BinE ((`AddOp | `SubOp | `MulOp | `DivOp | `ModOp), _, left, right) ->
      let left, right = runtime_type ctx left, runtime_type ctx right in
      if not (C.Eq.eq_typ left right) then
        unsupported e.at "arithmetic with mixed Nat/Int runtime types";
      left
  | _ -> expand ctx (e.note $ e.at)

let reject_text_bytes ctx (t : C.typ) =
  if (expand ctx t).it = C.TextT then
    unsupported t.at
      "byte text indexing, slicing and updates: Lean UTF-8 strings cannot represent every SpecTecX byte result"

let require_runtime_annotation ctx (value : C.exp) =
  if not (C.Eq.eq_typ (runtime_type ctx value) (expand ctx (value.note $ value.at))) then
    unsupported value.at
      "value with a different runtime type; use an explicit int cast for negated naturals"

let rec exp ctx (e : C.exp) : S.exp =
  let recurse = exp ctx in
  let component (value : C.exp) =
    require_runtime_annotation ctx value;
    recurse value in
  let node = match e.it with
  | C.BoolE b -> S.BoolE b
  | C.NumE n -> S.NumE n
  | C.TextE t ->
      if not (String.is_valid_utf_8 t) then
        unsupported e.at "text literal is not valid UTF-8 and cannot be represented by Lean String";
      S.TextE t
  | C.VarE id -> S.VarE id
  | C.UnE (op, t, e) -> S.UnE (op, t, recurse e)
  | C.BinE (op, t, l, r) -> S.BinE (op, t, recurse l, recurse r)
  | C.CmpE (op, t, l, r) -> S.CmpE (op, t, recurse l, recurse r)
  | C.UpCastE (t, e) -> S.UpCastE (typ t, recurse e)
  | C.DownCastE (t, e) -> S.DownCastE (typ t, recurse e)
  | C.SubE (e, t) ->
      let source = runtime_type ctx e in
      let value = { (recurse e) with note = typ_node e.at source.it } in
      S.SubE (value, typ t, subcheck ctx source t)
  | C.MatchE (e, p) -> S.MatchE (recurse e, pattern p)
  | C.TupleE es -> S.TupleE (List.map component es)
  | C.CaseE n -> S.CaseE (mixfix component n)
  | C.StrE fields -> S.StrE (List.map (fun (a,e) -> atom a, component e) fields)
  | C.OptE e -> S.OptE (Option.map component e)
  | C.ListE es -> S.ListE (List.map component es)
  | C.ConsE (l,r) -> S.ConsE (component l, recurse r)
  | C.CatE (l,r) -> S.CatE (recurse l, recurse r)
  | C.MemE (l,r) -> S.MemE (recurse l, recurse r)
  | C.LenE e -> S.LenE (recurse e)
  | C.DotE (e,a) -> S.DotE (recurse e, atom a)
  | C.IdxE (e,i) ->
      reject_text_bytes ctx (e.note $ e.at);
      S.IdxE (recurse e, recurse i)
  | C.SliceE (e,i,n) ->
      reject_text_bytes ctx (e.note $ e.at);
      S.SliceE (recurse e, recurse i, recurse n)
  | C.UpdE (e,p,v) -> S.UpdE (recurse e, path ctx p, component v)
  | C.CallE (id,ts,args) -> S.CallE (id, List.map typ ts, List.map (arg ctx) args)
  | C.IterE (e,(i,vs)) -> S.IterE (component e, (iter i, List.map var vs)) in
  node $$ (e.at, typ_node e.at e.note)

and path ctx (p : C.path) : S.path =
  (match p.it with
  | C.RootP -> S.RootP
  | C.IdxP (p,e) ->
      reject_text_bytes ctx (p.note $ p.at);
      S.IdxP (path ctx p, exp ctx e)
  | C.SliceP (p,i,n) ->
      reject_text_bytes ctx (p.note $ p.at);
      S.SliceP (path ctx p, exp ctx i, exp ctx n)
  | C.DotP (p,a) -> S.DotP (path ctx p, atom a))
  $$ (p.at, typ_node p.at p.note)

and pattern = function
  | C.CaseP n -> S.CaseP (mixfix Fun.id n)
  | C.ListP p -> S.ListP p
  | C.OptP p -> S.OptP p

and arg ctx (a : C.arg) : S.arg =
  (match a.it with
  | C.ExpA e -> require_runtime_annotation ctx e; S.ExpA (exp ctx e)
  | C.DefA id -> S.DefA id) $ a.at

(* Binding contexts are indexed by both identifier and iteration dimension,
   exactly like the current interpreter.  An IterE pattern binds only its
   collected outer variables, never the element variables in the parent scope. *)
let rec bind_pattern bound (e : C.exp) = match e.it with
  | C.VarE id -> Bindings.add (id.it, []) bound
  | C.TupleE es | C.ListE es -> List.fold_left bind_pattern bound es
  | C.CaseE notation -> List.fold_left bind_pattern bound (C.Mixfix.args notation)
  | C.StrE fields -> List.fold_left (fun b (_,e) -> bind_pattern b e) bound fields
  | C.OptE (Some e) | C.UpCastE (_,e) -> bind_pattern bound e
  | C.ConsE (l,r) | C.CatE (l,r) -> bind_pattern (bind_pattern bound l) r
  | C.IterE (_, (i,vars)) -> List.fold_left (fun b (v : C.var) ->
      Bindings.add (v.varid.it, v.iters @ [i]) b) bound vars
  | _ -> bound

let mode ctx id = match Hashtbl.find_opt ctx.relations id.it with
  | Some t -> t
  | None -> unsupported id.at ("unknown relation " ^ id.it)

let input_indices (t : C.reltyp) =
  C.Mixfix.args t.it |> List.mapi (fun i -> function C.Mode.In _ -> Some i | C.Mode.Out _ -> None)
  |> List.filter_map Fun.id

let rec premise ctx bound (p : C.prem) : S.prem * Bindings.t =
  let node, bound = match p.it with
  | C.RelPr {relid; notexp} ->
      let mode = mode ctx relid in
      let _, outputs = C.Mode.partition mode.it (C.Mixfix.args notexp) in
      S.RulePr (relid, mixfix (exp ctx) notexp, input_indices mode),
      List.fold_left bind_pattern bound outputs
  | C.RelAssertPr {call = {relid; notexp}; expect} ->
      let notation = mixfix (exp ctx) notexp in
      (if expect then S.IfHoldPr (relid, notation) else S.IfNotHoldPr (relid, notation)), bound
  | C.IfPr {cond; _} -> S.IfPr (exp ctx cond), bound
  | C.LetPr (l,r) ->
      let left, right = exp ctx l, exp ctx r in
      let binding = if ctx.ordered then S.LetPr (left,right) else
        S.IfPr (S.CmpE (`EqOp, `BoolT, left, right) $$ (p.at,S.BoolT)) in
      binding, bind_pattern bound l
  | C.DebugPr e -> S.DebugPr (exp ctx e), bound
  | C.ElsePr -> unsupported p.at "otherwise must be the final top-level premise"
  | C.IterPr (body, (i,vars)) ->
      let inputs, outputs = List.partition (fun (v : C.var) ->
        Bindings.mem (v.varid.it, v.iters @ [i]) bound) vars in
      if inputs = [] then unsupported p.at "iteration has no bound input variable";
      let inner = List.fold_left (fun b (v : C.var) ->
        Bindings.add (v.varid.it, v.iters) b) bound inputs in
      let body, _ = premise ctx inner body in
      let bound = List.fold_left (fun b (v : C.var) ->
        Bindings.add (v.varid.it, v.iters @ [i]) b) bound outputs in
      S.IterPr (body, (iter i, List.map var inputs, List.map var outputs)), bound in
  node $ p.at, bound

let without_fallback prems = match List.rev prems with
  | {it = C.ElsePr; _} :: rest -> true, List.rev rest
  | _ -> false, prems

let premises ctx bound prems =
  let original = prems in
  let fallback, prems = without_fallback prems in
  if fallback && not ctx.ordered then
    unsupported (List.hd (List.rev original)).at
      "declarative otherwise clauses; use the ordered ported backend";
  let rev, _ = List.fold_left (fun (acc,bound) p ->
    let p,bound = premise ctx bound p in p :: acc,bound) ([],bound) prems in
  List.rev rev

let fallback_order get_prems xs =
  let fallback,ordinary = List.partition (fun x -> fst (without_fallback (get_prems x))) xs in
  ordinary @ fallback

let rule ctx reltyp (r : C.rule) : S.rule =
  let inputs, outputs = C.Mode.partition reltyp.it (C.Mixfix.args r.it.concl) in
  List.iter (require_runtime_annotation ctx) outputs;
  let bound = List.fold_left bind_pattern Bindings.empty inputs in
  (r.it.ruleid, mixfix (exp ctx) r.it.concl, premises ctx bound r.it.prems) $ r.at

let clause ctx (c : C.clause) : S.clause =
  require_runtime_annotation ctx c.it.body;
  let bound = List.fold_left (fun bound (a : C.arg) -> match a.it with
    | C.ExpA e -> bind_pattern bound e | C.DefA _ -> bound) Bindings.empty c.it.args in
  (List.map (arg ctx) c.it.args, exp ctx c.it.body, premises ctx bound c.it.prems) $ c.at

let rec hint_exp (e : Lang.El.exp) : Lean_backend.Lang.El.exp =
  let module E = Lang.El in
  let module H = Lean_backend.Lang.El in
  (match e.it with
  | E.TextE s -> H.TextE s
  | E.AtomE a -> H.AtomE (atom a)
  | E.SeqE es -> H.SeqE (List.map hint_exp es)
  | E.BrackE (l,e,r) -> H.BrackE (atom l, hint_exp e, atom r)
  | E.HoleE h -> H.HoleE h
  | E.FuseE (l,r) -> H.FuseE (hint_exp l, hint_exp r)
  | _ -> H.RawE (E.Print.string_of_exp e)) $ e.at

let hints (hs : C.hint list) : S.hint list =
  List.filter_map (fun (h : C.hint) ->
    if h.hintid.it <> "print" then None else
    Some (Lean_backend.Lang.El.{hintid = h.hintid; hintexp = hint_exp h.hintexp}
      $ h.hintexp.at)) hs

let deftyp (t : C.deftyp) : S.deftyp =
  (match t.it with
  | C.PlainT t -> S.PlainT (typ t)
  | C.StructT fields -> S.StructT (List.map (fun (a,t) -> atom a,typ t) fields)
  | C.VariantT cases -> S.VariantT (List.map (fun (c : C.typcase) ->
      nottyp c.notation,
      ((c.origin.it.synid, List.map typ c.origin.it.targs) $ c.origin.at),
      hints c.hints) cases)) $ t.at

let translate ?(ordered = true) ?(builtin_profile = false) (source : C.spec) : S.spec =
  let ctx = {ordered; types = Hashtbl.create 32; relations = Hashtbl.create 32} in
  List.iter (fun (d : C.def) -> match d.it with
    | C.TypD {synid; tparams; deftyp} -> Hashtbl.replace ctx.types synid.it (tparams,deftyp)
    | C.RelD {relid; reltyp; _} -> Hashtbl.replace ctx.relations relid.it reltyp
    | _ -> ()) source;
  List.map (fun (d : C.def) ->
    (match d.it with
    | C.TypD {synid; tparams; deftyp = t} -> S.TypD (synid,tparams,deftyp t,[])
    | C.RelD {relid; reltyp; rules} ->
        let rules = fallback_order (fun (r : C.rule) -> r.it.prems) rules in
        let rules = List.map (rule ctx reltyp) rules in
        let group = (("" $ d.at),rules) $ d.at in
        S.RelD (relid, mixfix typ (C.Mode.notation reltyp.it) $ reltyp.at,
          input_indices reltyp, [group], None, [])
    | C.DecD {defid; tparams; params; typ = result; clauses} ->
        let clauses = fallback_order (fun (c : C.clause) -> c.it.prems) clauses in
        S.FuncDecD (defid,tparams,List.map param params,typ result,
          List.map (clause ctx) clauses,None,[])
    | C.BuiltinDecD {defid; tparams; params; typ = result; _} ->
        if not builtin_profile then unsupported d.at
          ("builtin $" ^ defid.it ^ " requires --builtin-profile donor; native SpecTecX does not define its implementation");
        if List.mem defid.it ["bits_to_int_unsigned"; "bits_to_int_signed";
          "int_to_bits_unsigned"; "int_to_bits_signed"] then (
          let bits = C.VarT {synid = "bits" $ d.at; targs = []} $ d.at in
          match (expand ctx bits).it with
          | C.IterT {typ = element; iter = C.List}
              when (expand ctx element).it = C.BoolT -> ()
          | _ -> unsupported d.at ("builtin $" ^ defid.it ^ " requires bits = bool*"));
        S.BuiltinDecD (defid,tparams,List.map param params,typ result,[])) $ d.at) source
