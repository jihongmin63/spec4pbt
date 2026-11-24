open Util.Source
open Lang
open Lang.Il
open Lang.Al
module Mixfix = Domain.Mixfix

type relation = {
  name : string;
  definition : def;
  inputs : Hints.Input.t;
  output_arity : int;
  output_types : typ list;
  calls : string list;
  defined : bool;
  is_function : bool;
}

module Collect = Lang.Al.Walk.Collect

let call_collector = { (Collect.make_base ~default:[] ~compose:( @ )) with
  collect_exp = (fun collector exp ->
    let nested = Collect.default_collect_exp collector exp in
    match exp.it with CallE (id, _, _) -> ("$" ^ id.it) :: nested | _ -> nested);
  collect_prem = (fun collector prem ->
    let nested = Collect.default_collect_prem collector prem in
    match prem.it with
    | RulePr (id, _, _) | IfHoldPr (id, _) | IfNotHoldPr (id, _) -> id.it :: nested
    | _ -> nested) }

let calls_exp exp = Collect.collect_exp call_collector exp
let calls_prem prem = Collect.collect_prem call_collector prem
let calls_prems prems = List.concat_map calls_prem prems
let calls_exps exps = List.concat_map calls_exp exps
let calls_args args = Collect.collect_args call_collector args

let calls_group group =
  let _, (_, inputs, match_prems), paths = group.it in
  calls_exps inputs @ calls_prems match_prems @
  List.concat_map (fun (_, prems, outputs) -> calls_prems prems @ calls_exps outputs) paths

let calls_clause clause =
  let args, output, prems = clause.it in
  calls_args args @ calls_prems prems @ calls_exp output

let relation_of_def def =
  let make name nottyp inputs calls defined =
    let args = Mixfix.args nottyp.it in
    let _, outputs = Hints.Input.split inputs args in
    {name = name.it; definition = def; inputs;
     output_arity = List.length outputs; output_types = outputs;
     calls = List.sort_uniq String.compare calls; defined; is_function = false}
  in
  let make_function id typ calls defined =
    {name = "$" ^ id.it; definition = def; inputs = [];
     output_arity = 1; output_types = [typ];
     calls = List.sort_uniq String.compare calls; defined; is_function = true}
  in
  match def.it with
  | ExternRelD (id, nottyp, inputs, _) -> Some (make id nottyp inputs [] false)
  | RelD (id, nottyp, inputs, groups, elsegroup, _) ->
      let calls = List.concat_map calls_group groups @
        (match elsegroup with
         | None -> []
         | Some group ->
             let _, (_, inputs, prems), (_, path_prems, outputs) = group.it in
             calls_exps inputs @ calls_prems (prems @ path_prems) @ calls_exps outputs) in
      Some (make id nottyp inputs calls true)
  | FuncDecD (id, _, _, typ, clauses, elseclause, _) ->
      let calls = List.concat_map calls_clause clauses @
        Option.fold ~none:[] ~some:calls_clause elseclause in
      Some (make_function id typ calls true)
  | ExternDecD (id, _, _, typ, _) -> Some (make_function id typ [] false)
  | _ -> None

let relations spec =
  let nodes = List.filter_map relation_of_def spec in
  let names = List.map (fun node -> node.name) nodes in
  (* Builtins have no authored relation bodies. Their expressions still
     execute normally, but are not internal relation-call edges. *)
  List.map (fun node -> {node with calls = List.filter (fun name ->
    not (String.starts_with ~prefix:"$" name) || List.mem name names) node.calls}) nodes

let find relations name =
  match List.filter (fun r -> r.name = name) relations with
  | [r] -> r
  | [] -> failwith ("unknown relation: " ^ name)
  | _ -> failwith ("ambiguous relation: " ^ name)

let reachable ?(stop_at = []) relations start =
  let rec walk seen = function
    | [] -> seen
    | name :: rest when List.mem name seen -> walk seen rest
    | name :: rest ->
        let relation = find relations name in
        let calls = if List.mem name stop_at then [] else relation.calls in
        walk (name :: seen) (calls @ rest)
  in
  walk [] [start]

let call_path ?(stop_at = []) relations start target =
  let rec walk seen = function
    | [] -> None
    | (name, path) :: _ when name = target -> Some (List.rev (name :: path))
    | (name, _) :: rest when List.mem name seen -> walk seen rest
    | (name, path) :: rest ->
        let relation = find relations name in
        let calls = if List.mem name stop_at then [] else relation.calls in
        let next = List.map (fun child -> child, name :: path) calls in
        walk (name :: seen) (rest @ next)
  in
  walk [] [start, []]

let classification_details relations explicit =
  List.map (fun relation ->
    let closure = reachable ~stop_at:explicit relations relation.name in
    let boundaries = List.filter (fun name -> List.mem name explicit) closure
      |> List.sort_uniq String.compare in
    let internal_calls = List.filter (fun name ->
        name <> relation.name &&
        not (find relations name).is_function &&
        not (List.exists (fun target -> List.mem target explicit)
          (reachable ~stop_at:explicit relations name))) closure
      |> List.sort_uniq String.compare in
    let flag = List.mem relation.name explicit ||
      (boundaries <> [] && internal_calls = []) in
    let kind = if List.mem relation.name explicit then "explicit_boundary"
      else if flag then "external_only_helper"
      else if boundaries <> [] then "mixed_helper" else "internal" in
    relation.name, flag, kind, boundaries, internal_calls) relations

let classify relations explicit =
  List.map (fun (name, flag, _, _, _) -> name, flag)
    (classification_details relations explicit)

let check_nested_boundaries relations explicit =
  List.iter (fun boundary ->
    let relation = find relations boundary in
    if relation.defined then
      List.iter (fun child ->
        if child <> boundary && List.mem child explicit then
          failwith (Printf.sprintf
            "%s: explicit external boundary contains nested boundary %s"
            boundary child))
        (reachable relations boundary)) explicit
