open Util.Source
open Lang.Il
open Lang.Al

type observation = { seq : int; label : string; source : string; value : Runtime.Value.t }
let events : observation list ref = ref []
type marker = { seq : int; phase : string; relation : string;
                kind : string; source : string; inputs : string list;
                outputs : string list; input_slots : string list list }
let markers : marker list ref = ref []
let sequence = ref 0
let tick () = incr sequence; !sequence

let record label source value =
  events := {seq = tick (); label; source; value} :: !events

let record_marker phase relation kind source inputs outputs input_slots =
  markers := {seq = tick (); phase; relation; kind; source;
              inputs = String.split_on_char ',' inputs |> List.filter ((<>) "");
              outputs = String.split_on_char ',' outputs |> List.filter ((<>) "");
              input_slots = Yojson.Safe.from_string input_slots
                |> Yojson.Safe.Util.to_list
                |> List.map (fun slot -> Yojson.Safe.Util.to_list slot
                  |> List.map Yojson.Safe.Util.to_string)}
             :: !markers

let reset () = events := []; markers := []; sequence := 0
let snapshot () = List.rev !events
let marker_snapshot () = List.rev !markers

let observed_types : (string * typ) list ref = ref []
let identity_types : (string * typ) list ref = ref []
let marker_name = "property_trace_marker"
let identity_prefix = "property_trace_identity_"
let function_names : string list ref = ref []
let occupied_names : string list ref = ref []
let temporary_counter = ref 0

let fresh_result exp =
  let rec choose () =
    let name = "property_trace_result_" ^ string_of_int !temporary_counter in
    incr temporary_counter;
    if List.mem name !occupied_names then choose () else name in
  let id = choose () $ exp.at in
  VarE id $$ (exp.at, exp.note)

(* Collect variable occurrences with their original type and source region.
   Reading these variables after a binding never reevaluates a constructor,
   projection, function call, or fresh operation in the original pattern. *)
let variables expressions =
  let module C = Lang.Al.Walk.Collect in
  let base = C.make_base ~default:[] ~compose:( @ ) in
  let collector = {base with C.collect_exp = (fun self exp ->
    match exp.it with
    | VarE _ -> [exp]
    | _ -> C.default_collect_exp self exp)} in
  let seen = Hashtbl.create 16 in
  C.collect_exps collector expressions |> List.filter (fun exp ->
    match exp.it with
    | VarE id when not (Hashtbl.mem seen id.it) ->
        Hashtbl.add seen id.it (); true
    | _ -> false)
let names exp =
  Lang.Al.Free.free_exp exp |> Domain.Lib.IdSet.elements
  |> List.map (fun id -> id.it)

let marker_call ?(input_slots = []) phase relation kind source inputs outputs at =
  let text_typ = Runtime.Type.Typ.Make.text in
  let bool_typ = Runtime.Type.Typ.Make.bool in
  let slots = `List (List.map (fun slot ->
    `List (List.map (fun name -> `String name) slot)) input_slots)
    |> Yojson.Safe.to_string in
  let args = [phase; relation; kind; source;
              String.concat "," inputs; String.concat "," outputs; slots]
    |> List.map (fun value -> ExpA (TextE value $$ (at, text_typ.it)) $ at) in
  IfPr (CallE (marker_name $ at, [], args) $$ (at, bool_typ.it)) $ at

let marker phase relation prem =
  let input_slots = match prem.it with
    | RulePr (_, notexp, hints) ->
        let input, _ = Lang.Hints.Input.split hints
          (Domain.Mixfix.args notexp) in
        List.map names input
    | LetPr (_, {it = CallE (_, _, args); _}) ->
        List.filter_map (fun arg -> match arg.it with
          | ExpA exp -> Some (names exp) | DefA _ -> None) args
    | IfHoldPr (_, notexp) | IfNotHoldPr (_, notexp) ->
        List.map names (Domain.Mixfix.args notexp)
    | _ -> [] in
  let kind, inputs, outputs = match prem.it with
    | RulePr (id, notexp, hints) ->
        let input, output = Lang.Hints.Input.split hints
          (Domain.Mixfix.args notexp) in
        id.it, List.concat_map names input,
        List.filter_map (fun exp -> match exp.it with
          | VarE id -> Some id.it | _ -> None) output
    | LetPr (left, right) ->
        (match right.it with
         | CallE (id, _, _) when String.starts_with ~prefix:"fresh" id.it -> "fresh"
         | CallE (id, _, _) when List.mem id.it !function_names -> "$" ^ id.it
         | _ -> "let"), names right, names left
    | IfPr exp -> "if", names exp, []
    | IfHoldPr (id, notexp) | IfNotHoldPr (id, notexp) ->
        id.it, List.concat_map names (Domain.Mixfix.args notexp), []
    | DebugPr exp -> "debug", names exp, []
    | IterPr _ -> "iter", [], [] in
  marker_call ~input_slots phase relation kind (string_of_region prem.at)
    inputs outputs prem.at

(* Traverse expressions in place. This only rebuilds their syntax: the native
   evaluator retains control over order, failures, and repeated evaluation. *)
let map_children f exp =
  let args args = List.map (fun arg -> match arg.it with
    | ExpA exp -> {arg with it = ExpA (f exp)} | DefA _ -> arg) args in
  let notexp exp = Domain.Mixfix.fill (Domain.Mixfix.to_mixop exp)
    (List.map f (Domain.Mixfix.args exp)) in
  let rec path p = {p with it = match p.it with
    | RootP -> RootP
    | IdxP (p, e) -> IdxP (path p, f e)
    | SliceP (p, l, h) -> SliceP (path p, f l, f h)
    | DotP (p, atom) -> DotP (path p, atom)} in
  {exp with it = match exp.it with
    | BoolE _ | NumE _ | TextE _ | VarE _ -> exp.it
    | UnE (op, typ, e) -> UnE (op, typ, f e)
    | BinE (op, typ, l, r) -> BinE (op, typ, f l, f r)
    | CmpE (op, typ, l, r) -> CmpE (op, typ, f l, f r)
    | UpCastE (typ, e) -> UpCastE (typ, f e)
    | DownCastE (typ, e) -> DownCastE (typ, f e)
    | SubE (e, typ, check) -> SubE (f e, typ, check)
    | MatchE (e, pattern) -> MatchE (f e, pattern)
    | TupleE es -> TupleE (List.map f es)
    | CaseE e -> CaseE (notexp e)
    | StrE fields -> StrE (List.map (fun (atom, e) -> atom, f e) fields)
    | OptE e -> OptE (Option.map f e)
    | ListE es -> ListE (List.map f es)
    | ConsE (h, t) -> ConsE (f h, f t)
    | CatE (l, r) -> CatE (f l, f r)
    | MemE (e, s) -> MemE (f e, f s)
    | LenE e -> LenE (f e)
    | DotE (e, atom) -> DotE (f e, atom)
    | IdxE (e, i) -> IdxE (f e, f i)
    | SliceE (e, l, h) -> SliceE (f e, f l, f h)
    | UpdE (e, p, v) -> UpdE (f e, path p, f v)
    | CallE (id, types, actuals) -> CallE (id, types, args actuals)
    | IterE (e, iter) -> IterE (f e, iter)}

(* Synthetic names exist only in dependency markers, never in executable AL.
   A wrapped call's result replaces its argument names in its enclosing
   expression, so a function can correctly discard an external argument. *)
let rec dependency_exp exp = match exp.it with
  | CallE (id, _, [_; _; {it = ExpA {it = CallE (_, _, args); _}; _}])
      when String.starts_with ~prefix:identity_prefix id.it ->
      (match (List.nth args 5).it with
       | ExpA {it = TextE output; _} -> VarE (output $ exp.at) $$ (exp.at, exp.note)
       | _ -> assert false)
  | _ -> map_children dependency_exp exp

let marker_exp phase relation prem = match (marker phase relation prem).it with
  | IfPr exp -> exp | _ -> assert false

let rec instrument_exp relation exp =
  let exp = map_children (instrument_exp relation) exp in
  match exp.it with
  | CallE (id, _, _) when List.mem id.it !function_names ||
      String.starts_with ~prefix:"fresh" id.it ->
      let output = fresh_result exp in
      let dependency = LetPr (output, dependency_exp exp) $ exp.at in
      let before = marker_exp "before" relation dependency in
      let after = marker_exp "after" relation dependency in
      let typ = exp.note $ exp.at in
      let key = Lang.Al.Print.string_of_typ typ in
      let builtin = identity_prefix ^ Digest.to_hex (Digest.string key) in
      if not (List.mem_assoc builtin !identity_types) then
        identity_types := (builtin, typ) :: !identity_types;
      let args = List.map (fun e -> ExpA e $ e.at) [before; exp; after] in
      CallE (builtin $ exp.at, [], args) $$ (exp.at, exp.note)
  | _ -> exp

let rec map_prem_inputs f prem =
  let notation f notexp = Domain.Mixfix.fill (Domain.Mixfix.to_mixop notexp)
    (List.map f (Domain.Mixfix.args notexp)) in
  {prem with it = match prem.it with
    | LetPr (left, right) -> LetPr (left, f right)
    | IfPr exp -> IfPr (f exp)
    | DebugPr exp -> DebugPr (f exp)
    | RulePr (id, notexp, hints) ->
        let actuals = Domain.Mixfix.args notexp in
        let inputs, outputs = Lang.Hints.Input.split hints actuals in
        let inputs = List.map f inputs in
        let actuals = Lang.Hints.Input.combine hints inputs outputs in
        RulePr (id, Domain.Mixfix.fill (Domain.Mixfix.to_mixop notexp) actuals, hints)
    | IfHoldPr (id, notexp) -> IfHoldPr (id, notation f notexp)
    | IfNotHoldPr (id, notexp) -> IfNotHoldPr (id, notation f notexp)
    | IterPr (inner, iter) -> IterPr (map_prem_inputs f inner, iter)}

let observe label exp =
  let typ = exp.note $ exp.at in
  let key = Lang.Al.Print.string_of_typ typ in
  let builtin = "property_observe_" ^ Digest.to_hex (Digest.string key) in
  if not (List.mem_assoc builtin !observed_types) then
    observed_types := (builtin, typ) :: !observed_types;
  let text_typ = Runtime.Type.Typ.Make.text in
  let bool_typ = Runtime.Type.Typ.Make.bool in
  let name_exp = TextE label $$ (exp.at, text_typ.it) in
  let args = [ExpA name_exp $ exp.at; ExpA exp $ exp.at] in
  let call = CallE (builtin $ exp.at, [], args) $$ (exp.at, bool_typ.it) in
  IfPr call $ exp.at

let observe_variables prefix expressions =
  List.map (fun exp -> match exp.it with
    | VarE id -> observe (prefix ^ id.it) exp
    | _ -> assert false) (variables expressions)

let after_prem relation prem =
  let outputs = match prem.it with
    | RulePr (_, notexp, inputs) ->
        let args = Domain.Mixfix.args notexp in
        snd (Lang.Hints.Input.split inputs args)
    | LetPr (left, _) -> [left]
    | _ -> [] in
  let prem = map_prem_inputs (instrument_exp relation) prem in
  let dependency = map_prem_inputs dependency_exp prem in
  marker "before" relation dependency :: prem ::
  marker "after" relation dependency :: observe_variables (relation ^ ".") outputs

let instrument_returns relation outputs =
  List.mapi (fun index exp ->
    let evaluation, value, suffix = match exp.it with
      | VarE id -> [], exp, id.it
      | _ ->
          let value = fresh_result exp in
          let binding = LetPr (value, exp) $ exp.at in
          after_prem relation binding, value, string_of_int index in
    let returned = marker_call "return" relation ("return:" ^ string_of_int index)
      (string_of_region exp.at) (names value) [] exp.at in
    evaluation @ [returned; observe (relation ^ ".return." ^ suffix) value], value)
    outputs
  |> List.split |> fun (premises, values) -> List.concat premises, values

let instrument_path relation inputs (id, prems, outputs) =
  let begin_path = marker_call ~input_slots:(List.map names inputs)
    "path_begin" relation ("path:" ^ id.it)
    (string_of_region id.at) (List.concat_map names inputs) [] id.at in
  let end_path = marker_call "path_end" relation ("path:" ^ id.it)
    (string_of_region id.at) [] [] id.at in
  let returns, outputs = instrument_returns relation outputs in
  let prems = begin_path :: observe_variables (relation ^ ".input.") inputs @
    List.concat_map (after_prem relation) prems @ returns @ [end_path] in
  id, prems, outputs

let instrument_group relation group =
  let id, (signature, inputs, match_prems), paths = group.it in
  (* The native runner evaluates match_prems before each attempted path.
     Moving that same list after the path marker exposes failures during
     matching without adding another attempt or changing evaluation order. *)
  let paths = List.map (fun (pid, prems, outputs) ->
    instrument_path relation inputs (pid, match_prems @ prems, outputs)) paths in
  {group with it = (id, (signature, inputs, []), paths)}

let first_order parameters = List.for_all (fun parameter ->
  match parameter.it with ExpP _ -> true | DefP _ -> false) parameters

let instrument_clause relation index clause =
  let args, output, prems = clause.it in
  let inputs = List.filter_map (fun arg ->
    match arg.it with ExpA exp -> Some exp | DefA _ -> None) args in
  let id = ("clause:" ^ string_of_int index) $ clause.at in
  let _, prems, outputs = instrument_path relation inputs (id, prems, [output]) in
  {clause with it = (args, List.hd outputs, prems)}

let instrument_def def =
  match def.it with
  | RelD (id, nottyp, inputs, groups, elsegroup, hints) ->
      let groups = List.map (instrument_group id.it) groups in
      let elsegroup = Option.map (fun group ->
        let gid, (signature, inputs, match_prems), (pid, prems, outputs) = group.it in
        {group with it = (gid, (signature, inputs, []),
          instrument_path id.it inputs (pid, match_prems @ prems, outputs))})
        elsegroup in
      {def with it = RelD (id, nottyp, inputs, groups, elsegroup, hints)}
  | FuncDecD (id, [], parameters, typ, clauses, elseclause, hints)
      when first_order parameters ->
      let relation = "$" ^ id.it in
      let clauses = List.mapi (instrument_clause relation) clauses in
      let elseclause = Option.map (instrument_clause relation (-1)) elseclause in
      {def with it = FuncDecD (id, [], parameters, typ, clauses, elseclause, hints)}
  | _ -> def

let builtin_def (name, typ) =
  let at = no_region in
  let text_typ = Runtime.Type.Typ.Make.text in
  let bool_typ = Runtime.Type.Typ.Make.bool in
  BuiltinDecD (name $ at, [],
    [ExpP text_typ $ at; ExpP typ $ at], bool_typ, []) $ at

let marker_def () =
  let at = no_region in
  let text_typ = Runtime.Type.Typ.Make.text in
  let bool_typ = Runtime.Type.Typ.Make.bool in
  BuiltinDecD (marker_name $ at, [],
    List.init 7 (fun _ -> ExpP text_typ $ at), bool_typ, []) $ at

let identity_def (name, typ) =
  let at = no_region in
  let bool_typ = Runtime.Type.Typ.Make.bool in
  BuiltinDecD (name $ at, [],
    [ExpP bool_typ $ at; ExpP typ $ at; ExpP bool_typ $ at], typ, []) $ at

let instrument spec =
  observed_types := [];
  identity_types := [];
  temporary_counter := 0;
  occupied_names := List.concat_map (fun def -> Lang.Al.Free.free_def def
    |> Domain.Lib.IdSet.elements |> List.map (fun id -> id.it)) spec;
  function_names := List.filter_map (fun def -> match def.it with
    | FuncDecD (id, [], parameters, _, _, _, _) when first_order parameters -> Some id.it
    | _ -> None) spec;
  let transformed = List.map instrument_def spec in
  transformed @ marker_def () ::
    (List.map builtin_def !observed_types @ List.map identity_def !identity_types)
