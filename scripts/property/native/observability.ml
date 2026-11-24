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
let current_premise : Yojson.Safe.t option ref = ref None
let last_failure : Yojson.Safe.t option ref = ref None
let analysis_snapshot : (unit -> Yojson.Safe.t) ref = ref (fun () -> `Assoc [])

let failure_evidence () = !last_failure
let strings values = `List (List.map (fun value -> `String value)
  (List.sort_uniq String.compare values))

let names exp =
  Lang.Al.Free.free_exp exp |> IdSet.elements |> List.map (fun id -> id.it)

let state_evidence state kind required source =
  `Assoc ["relation", `String !current_relation;
          "kind", `String kind; "source", `String source;
          "required", strings required;
          "known_before", strings state.known;
          "producers", `Assoc (List.map (fun (name, producer) ->
            name, `Assoc ["relation", `String producer.relation;
                           "source", `String producer.source;
                           "output_position", `Int producer.slot]) state.producers)]

let premise_evidence state prem =
  let kind, required, inputs = match prem.it with
    | RulePr (id, notexp, inputs) ->
        let args, _ = Hints.Input.split inputs (Mixfix.args notexp) in
        let positions = List.mapi (fun position exp ->
          `Assoc ["input_position", `Int position;
                  "variables", strings (names exp);
                  "source", `String (string_of_region exp.at)]) args in
        id.it, List.concat_map names args, positions
    | LetPr (_, right) -> "let", names right, []
    | IfPr exp -> "if", names exp, []
    | DebugPr exp -> "debug", names exp, []
    | IfHoldPr (id, notexp) | IfNotHoldPr (id, notexp) ->
        id.it, List.concat_map names (Mixfix.args notexp), []
    | IterPr _ -> "iter", [], [] in
  let fields = Yojson.Safe.Util.to_assoc
    (state_evidence state kind required (string_of_region prem.at)) in
  `Assoc (("inputs", `List inputs) :: fields)

let describe_missing state name source =
  let detail = match List.assoc_opt name state.producers with
  | Some producer ->
      Printf.sprintf "unavailable %s at %s; producer %s output slot %d at %s"
        name source producer.relation producer.slot producer.source
  | None -> Printf.sprintf "unavailable %s at %s" name source in
  detail ^ "; known before: " ^
    String.concat ", " (List.sort_uniq String.compare state.known)

let require summaries state strict exp =
  let missing = List.filter (fun name -> not (List.mem name state.known))
    (names exp) in
  match missing with
  | [] ->
      List.for_all (fun name ->
        match List.assoc_opt name summaries with
        | Some positions when not (List.mem 0 positions) ->
            if strict then failwith (Printf.sprintf
              "unavailable function %s return slot 0 at %s" name (string_of_region exp.at));
            false
        | _ -> true) (External_analysis.calls_exp exp)
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
  if strict then current_premise := Some (premise_evidence state prem);
  let after = match prem.it with
  | RulePr (id, notexp, inputs) ->
      let args = Mixfix.args notexp in
      let args_input, args_output = Hints.Input.split inputs args in
      let output_names = List.filter_map (fun exp ->
        match exp.it with VarE name -> Some name.it | _ -> None) args_output in
      let inputs_ready = List.for_all (fun (slot, exp) ->
        try require summaries state strict exp with
        | Failure message ->
            failwith (Printf.sprintf "consumer %s input slot %d: %s" id.it slot message))
        (List.mapi (fun slot exp -> slot, exp) args_input) in
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
            else (ignore (require summaries state strict exp); state))
        state (List.mapi (fun slot exp -> slot, exp) args_output)
  | LetPr (left, right) ->
      let ready = require summaries state strict right in
      (match left.it with
       | VarE id when ready -> bind state id.it
       | VarE _ -> state
       | _ -> if strict then
           failwith ("unsupported binding pattern at " ^ string_of_region left.at)
         else state)
  | IfPr exp | DebugPr exp ->
      ignore (require summaries state strict exp); state
  | IfHoldPr (id, notexp) | IfNotHoldPr (id, notexp) ->
      List.iter (fun exp -> ignore (require summaries state strict exp))
        (Mixfix.args notexp);
      ignore id; state
  | IterPr _ ->
      if strict then failwith ("iteration is outside property scope at " ^
        string_of_region prem.at) else state
  in
  if strict then begin
    let fields = Yojson.Safe.Util.to_assoc (premise_evidence state prem) in
    premise_trace := `Assoc (fields @ [
      "introduced", strings (List.filter (fun x -> not (List.mem x before)) after.known);
      "known_after", strings after.known]) :: !premise_trace
  end;
  after

let analyze_path summaries strict public_outputs initial match_prems (id, prems, outputs) =
  let state = List.fold_left (analyze_prem summaries strict)
    initial (match_prems @ prems) in
  ignore id;
  let positions = List.filter_map (fun (index, exp) ->
    if strict then current_premise := Some (state_evidence state
      ("return:" ^ string_of_int index) (names exp) (string_of_region exp.at));
    if require summaries state false exp then Some index else begin
      if strict && public_outputs then begin
        let missing = List.filter (fun name -> not (List.mem name state.known))
          (names exp) in
        let details = List.map (fun name ->
          describe_missing state name (string_of_region exp.at)) missing in
        failwith (Printf.sprintf "%s public output slot %d unavailable at %s; %s"
          !current_relation index (string_of_region exp.at)
          (String.concat "; " details))
      end;
      (* An unused simple return can be projected away. Computing a return
         still consumes all its operands, even if its slot is unavailable. *)
      (match exp.it with VarE _ -> ()
       | _ -> ignore (require summaries state strict exp));
      None
    end)
    (List.mapi (fun index exp -> index, exp) outputs) in
  positions, state

let intersect left right = List.filter (fun x -> List.mem x right) left

let analyze_defined ?(public_outputs = false) summaries strict relation =
  current_relation := relation.External_analysis.name;
  if strict then current_premise := None;
  let collect_group group =
    let _, (_, inputs, match_prems), paths = group.it in
    let initial =
      {known = List.concat_map names inputs; producers = []} in
    List.map (analyze_path summaries strict public_outputs initial match_prems) paths
  in
  let results = match relation.External_analysis.definition.it with
    | RelD (_, _, _, groups, elsegroup, _) ->
        let normal = List.concat_map collect_group groups in
        let fallback = match elsegroup with
          | None -> []
          | Some group ->
              let _, (_, inputs, match_prems), path = group.it in
              let initial = {known = List.concat_map names inputs; producers = []} in
              [analyze_path summaries strict public_outputs initial match_prems path] in
        normal @ fallback
    | FuncDecD (id, _, _, _, clauses, elseclause, _) ->
        let analyze_clause clause =
          let args, output, prems = clause.it in
          let inputs = List.filter_map (fun arg -> match arg.it with
            | ExpA exp -> Some exp | DefA _ -> None) args in
          let initial = {known = List.concat_map names inputs; producers = []} in
          (* A function always evaluates and returns one value; only dead
             relation outputs inside its body can be projected away. *)
          analyze_path summaries strict true initial [] (id, prems, [output]) in
        List.map analyze_clause clauses @
        Option.fold ~none:[] ~some:(fun clause -> [analyze_clause clause]) elseclause
    | _ -> [] in
  match results with
  | [] -> []
  | (positions, _) :: rest ->
      List.fold_left (fun current (next, _) -> intersect current next)
        positions rest

let output_positions relation =
  List.init relation.External_analysis.output_arity Fun.id

let analyze_impl spec pre goal explicit =
  premise_trace := [];
  current_premise := None;
  last_failure := None;
  analysis_snapshot := (fun () -> `Assoc []);
  let relations = External_analysis.relations spec in
  let explicit_names = List.map fst explicit in
  let details = External_analysis.classification_details relations explicit_names in
  let classification = List.map (fun (name, flag, _, _, _) -> name, flag) details in
  let has_external relation =
    List.exists (fun name -> List.mem name explicit_names)
      (External_analysis.reachable ~stop_at:explicit_names relations
        relation.External_analysis.name) in
  let summaries = ref (List.map (fun relation ->
    let name = relation.External_analysis.name in
    let positions = match List.assoc_opt name explicit with
      | Some keep -> keep
      | None -> if not (has_external relation)
        then output_positions relation else [] in
    name, positions) relations) in
  let report () =
    let assoc_int_list pairs = `Assoc (List.map (fun (name, positions) ->
      name, `List (List.map (fun x -> `Int x) positions)) pairs) in
    let reasons = `Assoc (List.map (fun (name, _, kind, boundaries, internal_calls) ->
      let relation = External_analysis.find relations name in
      name, `Assoc ["kind", `String kind; "boundaries", strings boundaries;
                    "internal_calls", strings internal_calls;
                    "source", `String (string_of_region relation.External_analysis.definition.at)])
      details) in
    let manifest = `Assoc (List.map (fun relation ->
      let name = relation.External_analysis.name in
      let positions = List.assoc name !summaries in
      let mapping = List.mapi (fun projected original -> original, projected) positions in
      name, `List (List.mapi (fun original typ ->
        `Assoc ["original_position", `Int original;
                "projected_position", (match List.assoc_opt original mapping with
                  | Some position -> `Int position | None -> `Null);
                "type", `String (Lang.Al.Print.string_of_typ typ);
                "source", `String (string_of_region typ.at)])
        relation.External_analysis.output_types)) relations) in
    `Assoc ["guaranteed_outputs", assoc_int_list !summaries;
            "projection", assoc_int_list !summaries;
            "projection_manifest", manifest;
            "classification_reasons", reasons;
            "premises", `List (List.rev !premise_trace);
            "external_classification", `Assoc (List.map (fun (name, flag) ->
              name, `Bool flag) classification)]
  in
  analysis_snapshot := report;
  External_analysis.check_nested_boundaries relations explicit_names;
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
    (External_analysis.reachable ~stop_at:explicit_names relations pre @
     External_analysis.reachable ~stop_at:explicit_names relations goal) in
  let with_path name action =
    try action () with Failure message ->
      let paths = List.filter_map (fun start ->
        External_analysis.call_path ~stop_at:explicit_names relations start name)
        [pre; goal] in
      let paths = List.sort (fun left right ->
        compare (List.length left) (List.length right)) paths in
      let path = match paths with first :: _ -> first | [] -> [name] in
      let fields = Yojson.Safe.Util.to_assoc (report ()) in
      last_failure := Some (`Assoc (
        ("helper_path", `List (List.map (fun name -> `String name) path)) ::
        ("premise", Option.value ~default:`Null !current_premise) :: fields));
      failwith ("helper path: " ^ String.concat " -> " path ^ "; " ^ message)
  in
  List.iter (fun name ->
    with_path name (fun () ->
    let relation = External_analysis.find relations name in
    if not relation.External_analysis.defined &&
       not (List.mem name explicit_names) then
      failwith (Printf.sprintf
        "%s has no specification definition or external adapter at %s"
        name (string_of_region relation.External_analysis.definition.at)))) relevant;
  List.iter (fun name ->
    with_path name (fun () ->
    let relation = External_analysis.find relations name in
    if relation.External_analysis.defined && not (List.mem name explicit_names)
    then begin
      let result = analyze_defined ~public_outputs:(name = pre || name = goal)
        !summaries true relation in
      let required = if name = pre || name = goal then output_positions relation else [] in
      List.iter (fun slot ->
        if not (List.mem slot result) then
          failwith (Printf.sprintf "%s public output slot %d unavailable at %s"
            name slot (string_of_region relation.External_analysis.definition.at)))
        required
    end)) relevant;
  report ()

let analyze spec pre goal explicit =
  try analyze_impl spec pre goal explicit with
  | Failure _ as error ->
      if Option.is_none !last_failure then begin
        let fields = Yojson.Safe.Util.to_assoc (!analysis_snapshot ()) in
        last_failure := Some (`Assoc (
          ("helper_path", `List []) ::
          ("premise", Option.value ~default:`Null !current_premise) :: fields))
      end;
      raise error
