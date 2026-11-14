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

(* A finite status-only helper program. Bindings are evaluated simultaneously
   in the caller's context and then scoped to the callee. No output witnesses
   are invented, and normal failure is distinct from an execution error. *)
type execution =
  | Call of int * I.prem
  | Step of I.prem * execution
  | Bind of (I.id * I.exp) list * execution
  | All of execution list
  | Any of execution list
  | Not of execution

exception Unsupported_helper of string

let helper_execution spec names root =
  let unsupported message = raise (Unsupported_helper message) in
  let definitions = List.filter_map (fun (definition:I.def) -> match definition.it with
    | I.RelD (id,_,_,_,_,_) when List.mem id.it names -> Some (id.it, definition)
    | _ -> None) spec in
  let leaves = ref 0 and nodes = ref 0 in
  let bump () =
    incr nodes;
    if !nodes > 4096 then unsupported "helper execution exceeds 4096 nodes" in
  let input_args (prem:I.prem) = match prem.it with
    | I.RulePr (_,notation,inputs) ->
        List.mapi (fun i arg -> i,arg) (Domain.Mixfix.args notation)
        |> List.filter_map (fun (i,arg) -> if List.mem i inputs then Some arg else None)
    | I.IfHoldPr (_,notation) | I.IfNotHoldPr (_,notation) -> Domain.Mixfix.args notation
    | _ -> [] in
  let ensure_bound bound expression =
    if not (Domain.Lib.IdSet.for_all (fun id -> List.mem id.it bound)
              (I.Free.free_exp expression)) then
      unsupported "helper input reads a hidden output or an unbound local" in
  let rec expand seen (prem:I.prem) =
    bump ();
    match prem.it with
    | I.IfNotHoldPr (id,notation) ->
        Not (expand seen {prem with it = I.IfHoldPr (id,notation)})
    | I.RulePr (id,notation,_) | I.IfHoldPr (id,notation) ->
        (match List.assoc_opt id.it definitions with
        | None -> let index = !leaves in incr leaves; Call (index,prem)
        | Some definition ->
            if List.mem id.it seen then unsupported ("recursive helper " ^ id.it);
            let args = Domain.Mixfix.args notation in
            (match definition.it with
            | I.RelD (_,_,inputs,groups,None,_) ->
                if List.length inputs <> List.length args then
                  unsupported "helper outputs are not supported";
                let rules = List.concat_map (fun (group:I.rulegroup) -> snd group.it) groups in
                Any (List.map (fun (rule:I.rule) ->
                  bump ();
                  let _,head,prems = rule.it in
                  let heads = Domain.Mixfix.args head in
                  let ids = List.map (fun (arg:I.exp) -> match arg.it with
                    | I.VarE id when id.it <> "_" -> id
                    | _ -> unsupported "helper input patterns must be distinct variables") heads in
                  let bound = List.map (fun id -> id.it) ids in
                  if List.length (List.sort_uniq String.compare bound) <> List.length bound then
                    unsupported "helper input patterns must be distinct variables";
                  let outputs = Hashtbl.create 8 in
                  List.iter (fun (p:I.prem) ->
                    List.iter (ensure_bound bound) (input_args p);
                    match p.it with
                    | I.RulePr (_,notation,inputs) ->
                        List.iteri (fun i (arg:I.exp) -> if not (List.mem i inputs) then
                          match arg.it with
                          | I.VarE id when id.it = "_" -> ()
                          | I.VarE id when not (List.mem id.it bound) &&
                              not (Hashtbl.mem outputs id.it) -> Hashtbl.add outputs id.it ()
                          | _ -> unsupported "helper output constraints are not observable")
                          (Domain.Mixfix.args notation)
                    | I.IfHoldPr _ | I.IfNotHoldPr _ -> ()
                    | I.IfPr expression -> ensure_bound bound expression
                    | _ -> unsupported "unsupported helper premise (only calls and input guards are executable)") prems;
                  let inputs = List.map2 (fun id (arg:I.exp) -> id,(arg.note $ arg.at)) ids heads in
                  let goal = I.IfPr (I.BoolE true $$ (rule.at,I.BoolT)) $ rule.at in
                  let blocks = match Pass.algo_property spec (id,inputs,goal,prems) with
                    | Ok (blocks,_) -> blocks
                    | Error diagnostic -> unsupported (Diagnostic.Render.render_report
                        ~ansi:Diagnostic.Ansi.plain (Diagnostic.Report.singleton diagnostic)) in
                  let rec sequence = function
                    | [] -> All []
                    | (p:I.prem) :: rest ->
                        (match p.it with
                        | I.IfPr _ | I.LetPr _ -> bump (); Step (p,sequence rest)
                        | _ ->
                            let first = expand (id.it :: seen) p in
                            let rest = sequence rest in
                            All [first;rest]) in
                  Bind (List.combine ids args, sequence (List.concat_map fst blocks))) rules)
            | _ -> unsupported "helper else rules are not supported"))
    | _ -> unsupported "unsupported helper execution premise" in
  expand [] root

let rec execution_leaves = function
  | Call (index,prem) -> [index,prem]
  | Step (_,tree) | Bind (_,tree) | Not tree -> execution_leaves tree
  | All trees | Any trees -> List.concat_map execution_leaves trees

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
