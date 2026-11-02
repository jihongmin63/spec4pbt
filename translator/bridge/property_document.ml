(** Read an authored property document without allowing it to rewrite the
    pinned specification. The patched frontend uses the ordinary definition
    grammar for helper relations and returns property clauses separately. *)
open Util.Source
module E = Lang.El
module I = Lang.Il

let fail at message =
  let location = Util.Source.string_of_region at in
  raise (Failure (location ^ ": " ^ message))

let read path =
  let channel = open_in_bin path in
  Fun.protect ~finally:(fun () -> close_in channel)
    (fun () -> really_input_string channel (in_channel_length channel))

let parse path parser =
  let lex = Lexing.from_string (read path) in
  lex.lex_curr_p <- {lex.lex_curr_p with pos_fname = path};
  try parser Frontend.Lexer.token lex with
  | Frontend.Parser.Error -> fail (Frontend.Lexer.region lex) "invalid property document syntax"

let relation_name (definition : E.def) =
  match definition.it with
  | E.RelD (id,_,_) | E.ExternRelD (id,_,_) -> Some id.it
  | _ -> None

let delegate (definition : I.def) = match definition.it with
  | I.RelD (_, _, inputs, groups, None, _) ->
      let rules = List.concat_map (fun (group:I.rulegroup) ->
        let _, rules = group.it in rules) groups in
      (match rules with
      | [rule] ->
          let _, pattern, prems = rule.it in
          let head_args = Domain.Mixfix.args pattern in
          if List.length inputs <> List.length head_args then None else
          (match prems with
          | [prem] ->
              let call = match prem.it with
                | I.RulePr (target, invocation, call_inputs) ->
                    Some (target, invocation, call_inputs, false)
                | I.IfNotHoldPr (target, invocation) ->
                    let inputs = List.init (List.length (Domain.Mixfix.args invocation)) Fun.id in
                    Some (target, invocation, inputs, true)
                | _ -> None in
              (match call with
              | Some (target, invocation, call_inputs, negative) ->
                  let call_args = Domain.Mixfix.args invocation in
                  if List.length call_inputs <> List.length head_args then None else
                  let same_variable head call = match head.it, call.it with
                    | I.VarE a, I.VarE b -> a.it = b.it
                    | _ -> false in
                  let matching_inputs = List.for_all2 (fun head_slot call_slot ->
                    try same_variable (List.nth head_args head_slot) (List.nth call_args call_slot)
                    with _ -> false) inputs call_inputs in
                  let head_names = List.filter_map (fun (arg:I.exp) -> match arg.it with
                    | I.VarE id -> Some id.it | _ -> None) head_args in
                  let seen_outputs = Hashtbl.create 4 in
                  let unconstrained_outputs = List.mapi (fun slot (arg:I.exp) ->
                    if List.mem slot call_inputs then true else
                    match arg.it with
                    | I.VarE id when id.it = "_" -> true
                    | I.VarE id when not (List.mem id.it head_names) &&
                        not (Hashtbl.mem seen_outputs id.it) ->
                        Hashtbl.add seen_outputs id.it (); true
                    | _ -> false) call_args |> List.for_all Fun.id in
                  if matching_inputs && unconstrained_outputs then Some (target.it, negative) else None
              | None -> None)
          | _ -> None)
      | _ -> None)
  | _ -> None

let delegate_target spec name primitive =
  let relations = List.filter_map (fun (definition:I.def) -> match definition.it with
    | I.RelD (id,_,_,_,_,_) -> Some (id.it, definition)
    | _ -> None) spec in
  let rec resolve seen inverted name =
    if name = primitive then Some (name, inverted) else
    if List.mem name seen then None else
    match List.assoc_opt name relations with
    | None -> None
    | Some relation -> Option.bind (delegate relation) (fun (next, negative) ->
        resolve (name :: seen) (inverted <> negative) next) in
  resolve [] false name

let load specs path =
  let source = match Pass.parse specs with
    | Ok x -> x
    | Error d ->
        raise (Failure (Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain
          (Diagnostic.Report.singleton d))) in
  let helpers = parse path Frontend.Parser.spec in
  let properties = parse path Frontend.Parser.properties in
  if properties = [] then fail (region_of_file path) "property document has no property clause";
  let original = Hashtbl.create 128 and authored = Hashtbl.create 16 in
  List.iter (fun definition -> Option.iter (fun name -> Hashtbl.replace original name ())
    (relation_name definition)) source;
  List.iter (fun (definition : E.def) -> match definition.it with
    | E.RelD (id,_,_) ->
        if Hashtbl.mem original id.it then fail id.at ("helper relation collides with source relation " ^ id.it);
        if Hashtbl.mem authored id.it then fail id.at ("duplicate helper relation " ^ id.it);
        Hashtbl.add authored id.it ()
    | E.RuleGroupD _ -> ()
    | _ -> fail definition.at "property document may only define helper relations and rules") helpers;
  List.iter (fun (definition : E.def) -> match definition.it with
    | E.RuleGroupD (id,_,_) ->
        if Hashtbl.mem original id.it then fail id.at ("helper rule changes source relation " ^ id.it);
        if not (Hashtbl.mem authored id.it) then fail id.at ("helper rule lacks authored relation " ^ id.it)
    | _ -> ()) helpers;
  source @ helpers, properties, Hashtbl.fold (fun name () names -> name :: names) authored []
