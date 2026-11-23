(* Projection of AL output slots for the native interpreter. A caller must
   supply a previously checked output manifest. *)
open Util.Source
open Lang.Il
open Lang.Al
module Mixfix = Domain.Mixfix

let selected map name = List.assoc_opt name map

let project_args inputs keep args =
  let out = ref 0 in
  let kept = ref [] in
  let new_inputs = ref [] in
  List.iteri (fun old_index arg ->
    let is_input = List.mem old_index inputs in
    let retain =
      if is_input then true
      else (let index = !out in incr out; List.mem index keep)
    in
    if retain then begin
      let new_index = List.length !kept in
      kept := arg :: !kept;
      if is_input then new_inputs := new_index :: !new_inputs
    end) args;
  List.rev !kept, List.rev !new_inputs

let project_mix inputs keep mix =
  let args, inputs = project_args inputs keep (Mixfix.args mix) in
  Mixfix.Seq (List.map (fun arg -> Mixfix.Arg arg) args), inputs

let project_prem map prem =
  match prem.it with
  | RulePr (id, notexp, inputs) ->
      (match selected map id.it with
      | None -> prem
      | Some keep ->
          let notexp, inputs = project_mix inputs keep notexp in
          {prem with it = RulePr (id, notexp, inputs)})
  | _ -> prem

let project_path map own_keep (id, prems, outputs) =
  let prems = List.map (project_prem map) prems in
  let outputs =
    match own_keep with
    | None -> outputs
    | Some keep ->
        List.filteri (fun index exp ->
          if List.mem index keep then true
          else match exp.it with
            | VarE _ -> false
            | _ -> failwith "cannot omit an effectful or computed return expression")
          outputs
  in
  id, prems, outputs

let project_group map own_keep group =
  let id, rulematch, paths = group.it in
  {group with it =
    (id, rulematch, List.map (project_path map own_keep) paths)}

let project_def map explicit def =
  match def.it with
  | ExternRelD (id, nottyp, inputs, hints) ->
      (match selected map id.it with
      | None -> def
      | Some keep ->
          let mix, inputs = project_mix inputs keep nottyp.it in
          {def with it = ExternRelD (id, mix $ nottyp.at, inputs, hints)})
  | RelD (id, nottyp, inputs, groups, elsegroup, hints) ->
      let own_keep = selected map id.it in
      let nottyp, inputs =
        match own_keep with
        | None -> nottyp, inputs
        | Some keep ->
            let mix, new_inputs = project_mix inputs keep nottyp.it in
            mix $ nottyp.at, new_inputs
      in
      let groups = List.map (project_group map own_keep) groups in
      let elsegroup = Option.map (fun group ->
        let id, rulematch, path = group.it in
        {group with it =
          (id, rulematch, project_path map own_keep path)}) elsegroup in
      if List.mem id.it explicit then
        {def with it = ExternRelD (id, nottyp, inputs, hints)}
      else
        {def with it = RelD (id, nottyp, inputs, groups, elsegroup, hints)}
  | _ -> def

let lower spec map explicit = List.map (project_def map explicit) spec
