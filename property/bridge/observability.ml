open Util.Source
open Lang
open Lang.Il
open Lang.Al

module Mixfix = Domain.Mixfix
module IdSet = Domain.Lib.IdSet

type producer = { relation : string; source : string; slot : int }
type state = { known : string list; producers : (string * producer) list }
let premise_trace : Yojson.Safe.t list ref = ref []
let current_relation = ref ""

let names exp =
  Lang.Al.Free.free_exp exp |> IdSet.elements |> List.map (fun id -> id.it)

let describe_missing state name source =
  match List.assoc_opt name state.producers with
  | Some producer ->
      Printf.sprintf "unavailable %s at %s; producer %s output slot %d at %s"
        name source producer.relation producer.slot producer.source
  | None -> Printf.sprintf "unavailable %s at %s" name source

let require state strict exp =
  let missing = List.filter (fun name -> not (List.mem name state.known))
    (names exp) in
  match missing with
  | [] -> true
  | name :: _ ->
      if strict then failwith (describe_missing state name (string_of_region exp.at));
      false

let bind state name =
  {state with known = if List.mem name state.known then state.known
                      else name :: state.known}

let producer state name relation source slot =
  {state with producers = (name, {relation; source; slot}) :: state.producers}

let analyze_prem summaries strict state prem =
  let before = state.known in
  let after = match prem.it with
  | RulePr (id, notexp, inputs) ->
      let args = Mixfix.args notexp in
      let args_input, args_output = Hints.Input.split inputs args in
      let output_names = List.filter_map (fun exp ->
        match exp.it with VarE name -> Some name.it | _ -> None) args_output in
      let inputs_ready = List.for_all (fun exp ->
        try require state strict exp with
        | Failure message ->
            failwith (Printf.sprintf "consumer %s: %s" id.it message))
        args_input in
      let guaranteed = Option.value ~default:[]
        (List.assoc_opt id.it summaries) in
      List.fold_left (fun state (slot, exp) ->
        match exp.it with
        | VarE name ->
            if strict && not (List.mem slot guaranteed) &&
               (List.mem name.it state.known ||
                List.length (List.filter ((=) name.it) output_names) > 1) then
              failwith (Printf.sprintf
                "unobserved equality pattern %s for %s output slot %d at %s"
                name.it id.it slot (string_of_region exp.at));
            let state =
              if List.mem slot guaranteed && inputs_ready
              then bind state name.it
              else producer state name.it id.it
                     (string_of_region id.at) slot in
            state
        | _ ->
            if not (List.mem slot guaranteed) then
              (if strict then failwith (Printf.sprintf
                "unobserved pattern for %s output slot %d at %s"
                id.it slot (string_of_region exp.at)) else state)
            else (ignore (require state strict exp); state))
        state (List.mapi (fun slot exp -> slot, exp) args_output)
  | LetPr (left, right) ->
      let ready = require state strict right in
      (match left.it with
       | VarE id when ready -> bind state id.it
       | VarE _ -> state
       | _ -> if strict then
           failwith ("unsupported binding pattern at " ^ string_of_region left.at)
         else state)
  | IfPr exp | DebugPr exp ->
      ignore (require state strict exp); state
  | IfHoldPr (id, notexp) | IfNotHoldPr (id, notexp) ->
      List.iter (fun exp -> ignore (require state strict exp))
        (Mixfix.args notexp);
      ignore id; state
  | IterPr _ ->
      if strict then failwith ("iteration is outside property scope at " ^
        string_of_region prem.at) else state
  in
  if strict then begin
    let kind, required = match prem.it with
      | RulePr (id, notexp, inputs) ->
          let args, _ = Hints.Input.split inputs (Mixfix.args notexp) in
          id.it, List.concat_map names args
      | LetPr (_, right) -> "let", names right
      | IfPr exp -> "if", names exp
      | DebugPr exp -> "debug", names exp
      | IfHoldPr (id, notexp) | IfNotHoldPr (id, notexp) ->
          id.it, List.concat_map names (Mixfix.args notexp)
      | IterPr _ -> "iter", [] in
    let strings xs = `List (List.map (fun x -> `String x)
      (List.sort_uniq String.compare xs)) in
    premise_trace := `Assoc [
      "relation", `String !current_relation;
      "kind", `String kind;
      "source", `String (string_of_region prem.at);
      "required", strings required;
      "known_before", strings before;
      "introduced", strings (List.filter (fun x -> not (List.mem x before)) after.known);
      "known_after", strings after.known] :: !premise_trace
  end;
  after

let analyze_path summaries strict initial match_prems (id, prems, outputs) =
  let state = List.fold_left (analyze_prem summaries strict)
    initial (match_prems @ prems) in
  ignore id;
  let positions = List.filter_map (fun (index, exp) ->
    if require state false exp then Some index else None)
    (List.mapi (fun index exp -> index, exp) outputs) in
  positions, state

let intersect left right = List.filter (fun x -> List.mem x right) left

let analyze_defined summaries strict relation =
  current_relation := relation.External_analysis.name;
  let collect_group group =
    let _, (_, inputs, match_prems), paths = group.it in
    let initial =
      {known = List.concat_map names inputs; producers = []} in
    List.map (analyze_path summaries strict initial match_prems) paths
  in
  let results = match relation.External_analysis.definition.it with
    | RelD (_, _, _, groups, elsegroup, _) ->
        let normal = List.concat_map collect_group groups in
        let fallback = match elsegroup with
          | None -> []
          | Some group ->
              let _, (_, inputs, match_prems), path = group.it in
              let initial = {known = List.concat_map names inputs; producers = []} in
              [analyze_path summaries strict initial match_prems path] in
        normal @ fallback
    | _ -> [] in
  match results with
  | [] -> []
  | (positions, _) :: rest ->
      List.fold_left (fun current (next, _) -> intersect current next)
        positions rest

let output_positions relation =
  List.init relation.External_analysis.output_arity Fun.id

let analyze spec pre goal explicit =
  premise_trace := [];
  let relations = External_analysis.relations spec in
  let explicit_names = List.map fst explicit in
  External_analysis.check_nested_boundaries relations explicit_names;
  let classification = External_analysis.classify relations explicit_names in
  let has_external relation =
    List.exists (fun name -> List.mem name explicit_names)
      (External_analysis.reachable relations relation.External_analysis.name) in
  let summaries = ref (List.map (fun relation ->
    let name = relation.External_analysis.name in
    let positions = match List.assoc_opt name explicit with
      | Some keep -> keep
      | None -> if not (has_external relation)
        then output_positions relation else [] in
    name, positions) relations) in
  let max_steps = 1 + List.fold_left (fun n r ->
    n + r.External_analysis.output_arity) 0 relations in
  let rec stabilize remaining =
    if remaining <= 0 then failwith "observation summary did not converge";
    let updated = List.map (fun relation ->
      let name = relation.External_analysis.name in
      let current = List.assoc name !summaries in
      if List.mem name explicit_names || not (has_external relation) ||
         not relation.External_analysis.defined
      then name, current
      else name, analyze_defined !summaries false relation)
      relations in
    if updated <> !summaries then (summaries := updated; stabilize (remaining-1))
  in
  stabilize max_steps;
  let relevant = List.sort_uniq String.compare
    (External_analysis.reachable relations pre @
     External_analysis.reachable relations goal) in
  List.iter (fun name ->
    let relation = External_analysis.find relations name in
    if not relation.External_analysis.defined &&
       not (List.mem name explicit_names) then
      failwith (Printf.sprintf
        "%s has no specification definition or external adapter at %s"
        name (string_of_region relation.External_analysis.definition.at))) relevant;
  List.iter (fun name ->
    let relation = External_analysis.find relations name in
    if relation.External_analysis.defined && not (List.mem name explicit_names)
    then begin
      let result = analyze_defined !summaries true relation in
      let required = if name = pre || name = goal then output_positions relation else [] in
      List.iter (fun slot ->
        if not (List.mem slot result) then
          failwith (Printf.sprintf "%s public output slot %d unavailable at %s"
            name slot (string_of_region relation.External_analysis.definition.at)))
        required
    end) relevant;
  let assoc_int_list pairs = `Assoc (List.map (fun (name, positions) ->
    name, `List (List.map (fun x -> `Int x) positions)) pairs) in
  `Assoc ["guaranteed_outputs", assoc_int_list !summaries;
          "projection", assoc_int_list !summaries;
          "premises", `List (List.rev !premise_trace);
          "external_classification", `Assoc (List.map (fun (name, flag) ->
            name, `Bool flag) classification)]
