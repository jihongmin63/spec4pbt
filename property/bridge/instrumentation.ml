open Util.Source
open Lang.Il
open Lang.Al

type observation = { seq : int; label : string; source : string; value : Runtime.Value.t }
let events : observation list ref = ref []
type marker = { seq : int; phase : string; relation : string;
                kind : string; source : string; inputs : string list;
                outputs : string list }
let markers : marker list ref = ref []
let sequence = ref 0
let tick () = incr sequence; !sequence

let record label source value =
  events := {seq = tick (); label; source; value} :: !events

let record_marker phase relation kind source inputs outputs =
  markers := {seq = tick (); phase; relation; kind; source;
              inputs = String.split_on_char ',' inputs |> List.filter ((<>) "");
              outputs = String.split_on_char ',' outputs |> List.filter ((<>) "")}
             :: !markers

let reset () = events := []; markers := []; sequence := 0
let snapshot () = List.rev !events
let marker_snapshot () = List.rev !markers

let observed_types : (string * typ) list ref = ref []
let marker_name = "property_trace_marker"
let names exp =
  Lang.Al.Free.free_exp exp |> Domain.Lib.IdSet.elements
  |> List.map (fun id -> id.it)

let marker_call phase relation kind source inputs outputs at =
  let text_typ = Runtime.Type.Typ.Make.text in
  let bool_typ = Runtime.Type.Typ.Make.bool in
  let args = [phase; relation; kind; source;
              String.concat "," inputs; String.concat "," outputs]
    |> List.map (fun value -> ExpA (TextE value $$ (at, text_typ.it)) $ at) in
  IfPr (CallE (marker_name $ at, [], args) $$ (at, bool_typ.it)) $ at

let marker phase relation prem =
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
         | _ -> "let"), names right,
        (match left.it with VarE id -> [id.it] | _ -> [])
    | IfPr exp -> "if", names exp, []
    | IfHoldPr (id, notexp) | IfNotHoldPr (id, notexp) ->
        id.it, List.concat_map names (Domain.Mixfix.args notexp), []
    | DebugPr exp -> "debug", names exp, []
    | IterPr _ -> "iter", [], [] in
  marker_call phase relation kind (string_of_region prem.at)
    inputs outputs prem.at

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

let after_prem relation prem =
  let vars = match prem.it with
    | RulePr (_, notexp, inputs) ->
        let args = Domain.Mixfix.args notexp in
        let _, outputs = Lang.Hints.Input.split inputs args in
        outputs
    | LetPr (left, _) -> [left]
    | _ -> [] in
  let observed = List.filter_map (fun exp ->
    match exp.it with
    | VarE id -> Some (observe (relation ^ "." ^ id.it) exp)
    | _ -> None) vars in
  marker "before" relation prem :: prem ::
  marker "after" relation prem :: observed

let instrument_path relation initial_inputs (id, prems, outputs) =
  let begin_path = marker_call "path_begin" relation ("path:" ^ id.it)
    (string_of_region id.at) initial_inputs [] id.at in
  let end_path = marker_call "path_end" relation ("path:" ^ id.it)
    (string_of_region id.at) [] [] id.at in
  let prems = begin_path :: List.concat_map (after_prem relation) prems in
  let return_markers = List.mapi (fun index exp ->
    marker_call "return" relation ("return:" ^ string_of_int index)
      (string_of_region exp.at) (names exp) [] exp.at) outputs in
  let final = List.filter_map (fun exp ->
    match exp.it with
    | VarE name -> Some (observe (relation ^ ".return." ^ name.it) exp)
    | _ -> None) outputs in
  id, prems @ return_markers @ final @ [end_path], outputs

let instrument_group relation group =
  let id, rulematch, paths = group.it in
  let _, inputs, _ = rulematch in
  let initial_inputs = List.concat_map names inputs in
  {group with it =
    (id, rulematch, List.map (instrument_path relation initial_inputs) paths)}

let instrument_def def =
  match def.it with
  | RelD (id, nottyp, inputs, groups, elsegroup, hints) ->
      let groups = List.map (instrument_group id.it) groups in
      let elsegroup = Option.map (fun group ->
        let gid, rulematch, path = group.it in
        let _, inputs, _ = rulematch in
        let initial_inputs = List.concat_map names inputs in
        {group with it = (gid, rulematch,
          instrument_path id.it initial_inputs path)})
        elsegroup in
      {def with it = RelD (id, nottyp, inputs, groups, elsegroup, hints)}
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
    List.init 6 (fun _ -> ExpP text_typ $ at), bool_typ, []) $ at

let instrument spec =
  observed_types := [];
  let transformed = List.map instrument_def spec in
  transformed @ marker_def () :: List.map builtin_def !observed_types
