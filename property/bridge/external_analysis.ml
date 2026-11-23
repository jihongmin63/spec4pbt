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
  calls : string list;
  defined : bool;
}

let rec calls_prem prem =
  match prem.it with
  | RulePr (id, _, _) | IfHoldPr (id, _) | IfNotHoldPr (id, _) -> [id.it]
  | IterPr (prem, _) -> calls_prem prem
  | _ -> []

let calls_group group =
  let _, (_, _, match_prems), paths = group.it in
  List.concat_map calls_prem match_prems @
  List.concat_map (fun (_, prems, _) -> List.concat_map calls_prem prems) paths

let relation_of_def def =
  let make name nottyp inputs calls defined =
    let args = Mixfix.args nottyp.it in
    let _, outputs = Hints.Input.split inputs args in
    {name = name.it; definition = def; inputs;
     output_arity = List.length outputs;
     calls = List.sort_uniq String.compare calls; defined}
  in
  match def.it with
  | ExternRelD (id, nottyp, inputs, _) -> Some (make id nottyp inputs [] false)
  | RelD (id, nottyp, inputs, groups, elsegroup, _) ->
      let calls = List.concat_map calls_group groups @
        (match elsegroup with
         | None -> []
         | Some group ->
             let _, (_, _, prems), (_, path_prems, _) = group.it in
             List.concat_map calls_prem (prems @ path_prems)) in
      Some (make id nottyp inputs calls true)
  | _ -> None

let relations spec = List.filter_map relation_of_def spec

let find relations name =
  match List.filter (fun r -> r.name = name) relations with
  | [r] -> r
  | [] -> failwith ("unknown relation: " ^ name)
  | _ -> failwith ("ambiguous relation: " ^ name)

let reachable relations start =
  let rec walk seen = function
    | [] -> seen
    | name :: rest when List.mem name seen -> walk seen rest
    | name :: rest ->
        let relation = find relations name in
        walk (name :: seen) (relation.calls @ rest)
  in
  walk [] [start]

let classify relations explicit =
  List.map (fun relation ->
    let closure = reachable relations relation.name in
    let reaches_boundary = List.exists (fun name -> List.mem name explicit) closure in
    let every_call_reaches_boundary =
      List.for_all (fun name ->
        name = relation.name ||
        List.exists (fun target -> List.mem target explicit)
          (reachable relations name)) closure in
    relation.name,
    (List.mem relation.name explicit ||
     (reaches_boundary && every_call_reaches_boundary))) relations

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
