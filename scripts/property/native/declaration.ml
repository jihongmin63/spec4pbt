(* Declaration wrappers use the native parser, type context and elaborator.
   This module supplies local witness declarations; it never evaluates terms. *)
open Util.Source
open Lang
open Lang.El
module E = Pass__Elaborate__Elab
module C = Pass__Elaborate__Ctx
module IdSet = Domain.Lib.IdSet
module MEnv = Runtime.Static.Envs.MEnv

let unwrap = function
  | Ok value -> value
  | Error error ->
      let report = P4spectec.Error.to_report error in
      failwith (Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain report)

let attempt value =
  let open Pass__Elaborate__Attempt in
  let+ value = value in value

(* Only expression variables and variable declarations are alpha-renamed.
   Native type/function/field identifiers have separate roles, even when their
   spelling coincides with a local variable. Keep every occurrence location. *)
let rec variable_ids_exp exp = match exp.it with
  | VarE id -> [id]
  | UnE (_, exp) | ArithE exp | LenE exp | DotE (exp, _)
  | ParenE exp | IterE (exp, _) | SubE (exp, _) | BrackE (_, exp, _)
  | UnparenE (_, exp) -> variable_ids_exp exp
  | BinE (left, _, right) | CmpE (left, _, right)
  | ConsE (left, right) | CatE (left, right) | IdxE (left, right)
  | MemE (left, right) | InfixE (left, _, right) | FuseE (left, _, right) ->
      variable_ids_exp left @ variable_ids_exp right
  | SliceE (base, left, right) ->
      List.concat_map variable_ids_exp [base; left; right]
  | ListE exps | TupleE exps | SeqE exps -> List.concat_map variable_ids_exp exps
  | StrE fields -> List.concat_map (fun (_, exp) -> variable_ids_exp exp) fields
  | UpdE (base, path, value) ->
      variable_ids_exp base @ variable_ids_path path @ variable_ids_exp value
  | CallE (_, _, args) -> List.concat_map (fun arg -> match arg.it with
      | ExpA exp -> variable_ids_exp exp | DefA _ -> []) args
  | BoolE _ | NumE _ | TextE _ | EpsE | AtomE _ | HoleE _ | LatexE _ -> []
and variable_ids_path path = match path.it with
  | RootP -> []
  | IdxP (path, exp) -> variable_ids_path path @ variable_ids_exp exp
  | SliceP (path, left, right) ->
      variable_ids_path path @ variable_ids_exp left @ variable_ids_exp right
  | DotP (path, _) -> variable_ids_path path

let rec variable_ids_prem prem = match prem.it with
  | VarPr (id, _) -> [id]
  | RulePr (_, exp) | RuleNotPr (_, exp) | IfPr exp | DebugPr exp ->
      variable_ids_exp exp
  | IterPr (prem, _) -> variable_ids_prem prem
  | ElsePr -> []

let names probe =
  let property = unwrap (P4spectec.parse [probe]) in
  let ids = List.concat_map (fun def -> match def.it with
    | RuleGroupD (_, _, rules) -> List.concat_map (fun rule ->
        let _, _, exp, prems = rule.it in
        variable_ids_exp exp @ List.concat_map variable_ids_prem prems) rules
    | _ -> []) property in
  let unique = IdSet.of_list ids |> IdSet.elements in
  `Assoc ["names", `List (List.map (fun id -> `String id.it) unique);
          "occurrences", `List (List.map (fun id ->
            `Assoc ["file", `String id.at.left.file;
                    "line", `Int id.at.left.line;
                    "column", `Int id.at.left.column]) ids)]

let run paths probe =
  let specification = unwrap (P4spectec.parse paths) in
  ignore (unwrap (P4spectec.elab paths));
  let ctx, _ = E.elab_defs (C.init ()) specification in
  let property = unwrap (P4spectec.parse [probe]) in
  let prems = List.concat_map (fun def -> match def.it with
    | RuleGroupD (_, _, rules) -> List.concat_map (fun rule ->
        let _, _, _, prems = rule.it in prems) rules
    | _ -> []) property in
  let ctx = ref ctx in
  let bound = ref IdSet.empty in
  let variables = ref [] in
  let register id typ =
    if IdSet.mem id !bound then
      failwith (string_of_region id.at ^ ": duplicate property variable " ^ id.it);
    (* A property has a local namespace, independent of specification metavariables. *)
    ctx := { !ctx with menv = MEnv.add id typ !ctx.menv };
    bound := IdSet.add id !bound;
    variables := !variables @ [id, typ]
  in
  let require exp =
    IdSet.iter (fun id -> if not (IdSet.mem id !bound) then
      failwith (string_of_region id.at ^ ": unbound property variable " ^ id.it))
      (El.Free.free_id_exp exp)
  in
  let rec slots notation exp =
    let open Domain.Mixfix in
    match notation, exp.it with
    | _, ParenE exp -> slots notation exp
    | Arg typ, _ -> Some [typ, exp]
    | Seq types, SeqE exps when List.length types = List.length exps ->
        let parts = List.map2 slots types exps in
        if List.for_all Option.is_some parts then
          Some (List.concat_map Option.get parts) else None
    | Infix (left, atom, right), InfixE (l, actual, r) when atom.it = actual.it ->
        (match slots left l, slots right r with
         | Some left, Some right -> Some (left @ right) | _ -> None)
    | Brack (left, inner, right), BrackE (actual_left, exp, actual_right)
      when left.it = actual_left.it && right.it = actual_right.it -> slots inner exp
    | Atom atom, AtomE actual when atom.it = actual.it -> Some []
    | _ -> None
  in
  let rec bind_pattern typ exp = match exp.it, typ.it with
    | VarE id, _ when not (IdSet.mem id !bound) -> register id typ
    | VarE _, _ -> ()
    | ParenE exp, _ -> bind_pattern typ exp
    | TupleE exps, Il.TupleT types when List.length exps = List.length types ->
        List.iter2 bind_pattern types exps
    | ListE exps, Il.IterT (element, _) -> List.iter (bind_pattern element) exps
    | _, Il.VarT (id, args) ->
        (match C.find_typdef !ctx id with
         | Runtime.Type.Typdef.Defined (params, definition) ->
             let theta = Domain.Lib.TIdMap.of_lists params args in
             let subst = Runtime.Type.Subst.subst_typ theta in
             (match definition.it with
              | Il.PlainT inner -> bind_pattern (subst inner) exp
              | Il.StructT fields ->
                  (match exp.it with
                   | StrE values -> List.iter (fun (atom, field_type) ->
                       match List.find_opt (fun (actual, _) -> atom.it = actual.it) values with
                       | Some (_, value) -> bind_pattern (subst field_type) value
                       | None -> ()) fields
                   | _ -> ())
              | Il.VariantT cases ->
                  let candidates = List.filter_map (fun case ->
                    let notation, _, _ = Runtime.Type.Subst.subst_typcase theta case in
                    slots notation.it exp) cases in
                  (match candidates with
                   | [fields] -> List.iter (fun (typ, value) -> bind_pattern typ value) fields
                   | _ when IdSet.subset (El.Free.free_id_exp exp) !bound -> ()
                   | [] -> () (* Native elaboration gives the notation diagnostic. *)
                   | _ -> failwith (string_of_region exp.at ^
                       ": ambiguous witness types; use an explicit -- var declaration")))
         | _ -> ())
    | _, _ -> ()
  in
  let last = List.length prems - 1 in
  List.iteri (fun index prem ->
    let goal = index = last in
    (match prem.it with
    | VarPr (id, typ) when not goal -> register id (E.elab_plaintyp !ctx typ)
    | RulePr (id, exp) when not goal ->
        let notation, inputs = C.find_rel_signature !ctx id in
        let args = Option.value ~default:[] (slots notation.it exp) in
        List.iteri (fun i (typ, value) ->
          if List.mem i inputs then require value else bind_pattern typ value) args;
        require exp
    | IfPr {it = CmpE (left, `EqOp, right); _} when not goal ->
        (* Infer a value with the native elaborator, then use that exact type
           to discover variables in the opposite pattern. Equality is symmetric. *)
        let infer_and_bind value pattern =
          if not (IdSet.subset (El.Free.free_id_exp pattern) !bound) &&
             IdSet.subset (El.Free.free_id_exp value) !bound then
            let _, _, typ = attempt (E.infer_exp !ctx value) in
            bind_pattern typ pattern
        in
        infer_and_bind right left;
        infer_and_bind left right;
        require left; require right
    | IfPr exp | RulePr (_, exp) | RuleNotPr (_, exp) | DebugPr exp -> require exp
    | _ -> ());
    if (match prem.it with VarPr _ -> false | _ -> true) then
      let next, _ = E.elab_prem !ctx prem in ctx := next
  ) prems;
  let goal_variables = match List.rev prems with
    | goal :: _ -> El.Free.free_id_prem goal |> IdSet.elements
    | [] -> [] in
  `Assoc ["goal_variables", `List (List.map (fun id -> `String id.it) goal_variables);
          "variables", `List (List.map (fun (id, typ) ->
    `Assoc ["name", `String id.it; "type", `String (Il.Print.string_of_typ typ);
            "source", `String (string_of_region id.at)]) !variables)]

let run paths probe =
  try run paths probe with Pass__Elaborate__Error.ElabError diagnostic ->
    let report = P4spectec.Error.to_report diagnostic in
    failwith (Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain report)
