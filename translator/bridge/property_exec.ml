(** Execute a certified property against a frozen external trace. All expression
    and premise evaluation goes through the official SpecTec AL interpreter. *)
open Util.Source
open Lang
module S = Lang.Il
module J = Yojson.Safe
module Run = Runtime.Dynamic_Runner.Signature
module Value = Runtime.Value
module B = Interp_al.Backtrack

let fail message = raise (Failure message)
let field key = function
  | `Assoc fields -> (try List.assoc key fields with Not_found -> fail ("missing field " ^ key))
  | _ -> fail "expected JSON object"
let text = function `String s -> s | _ -> fail "expected JSON string"
let array = function `List xs -> xs | _ -> fail "expected JSON array"
let object_fields = function `Assoc xs -> xs | _ -> fail "expected JSON object"
let unique_json j =
  let rec visit = function
    | `Assoc xs ->
        let names = List.map fst xs in
        if List.length (List.sort_uniq String.compare names) <> List.length names then
          fail "duplicate JSON field";
        List.iter (fun (_, v) -> visit v) xs
    | `List xs -> List.iter visit xs
    | _ -> () in
  visit j
let json_obj fields = `Assoc fields
let json_bool b = `Bool b
let report d = Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain (Diagnostic.Report.singleton d)

module NoExternal = struct
  module Cache = struct let cache_on () = () let cache_off () = () end
  let blocked name = Run.Fail (Run.abort ~source:"property" no_region
    ("unexpected external I/O while checking " ^ name))
  let eval_extern_rel name _ = blocked name
  let eval_extern_func name _ _ = blocked name
  let checkpoint () = 0
  let seff _ _ = false
  let clear () = ()
  let init_mode _ = Ok ()
end
module Eval = Interp_al.Interp.Make (Interface.SpecTec_AL) (NoExternal) ()

let checked = function
  | B.Ok x -> x
  | B.Unmatch _ -> fail "AL premise did not hold"
  | B.Err _ -> fail "AL premise evaluation error"

let parse_property specs path name =
  let spec_el, properties, _ = Property_document.load specs path in
  let spec_il = match Pass.elab_spec spec_el with Ok x -> x | Error d -> fail (report d) in
  let selected = List.filter (fun ((id:El.id),_,_,_) -> id.it = name) properties in
  let clause = match selected with [p] -> p | _ -> fail "property occurrence mismatch" in
  let ((_, inputs, _, _) as clause_il) =
    match Pass.elab_property spec_el clause with Ok x -> x | Error d -> fail (report d) in
  let blocks, goal = match Pass.algo_property spec_il clause_il with
    | Ok x -> x | Error d -> fail (report d) in
  let spec_al = match Pass.algo_spec spec_il with Ok x -> x | Error d -> fail (report d) in
  (inputs, blocks, goal, spec_il, spec_al)

let types spec =
  let table = Hashtbl.create 64 in
  List.iter (fun (definition:S.def) -> match definition.it with
    | TypD (id, _, body, _) -> Hashtbl.replace table id.it body
    | _ -> ()) spec;
  table

let bigint_json = function
  | `Int n -> Bigint.of_int n
  | `Intlit s -> Bigint.of_string s
  | _ -> fail "expected JSON integer"

let rec decode typedefs (typ:S.typ) json =
  match typ.it, json with
  | BoolT, `Bool b -> Value.Make.bool b
  | NumT `NatT, (`Int _ | `Intlit _) ->
      let n = bigint_json json in
      if Bigint.compare n Bigint.zero < 0 then fail "negative natural";
      Value.Make.nat n
  | NumT `IntT, (`Int _ | `Intlit _) -> Value.Make.int (bigint_json json)
  | TextT, `String s -> Value.Make.text s
  | TupleT ts, `List xs when List.length ts = List.length xs ->
      Value.Make.tuple typ (List.map2 (decode typedefs) ts xs)
  | IterT (t, List), `List xs ->
      Value.Make.list typ (List.map (decode typedefs t) xs)
  | IterT (_, Opt), `Null -> Value.Make.opt typ None
  | IterT (t, Opt), value -> Value.Make.opt typ (Some (decode typedefs t value))
  | VarT (id, []), _ -> (match Hashtbl.find_opt typedefs id.it with
      | Some {it = S.PlainT alias; _} -> decode typedefs alias json
      | Some {it = S.StructT fields; _} ->
          let actual = object_fields json in
          let expected = List.map (fun (atom,_) -> Domain.Atom.string_of_atom atom.it) fields in
          if List.sort String.compare expected <> List.sort String.compare (List.map fst actual) then
            fail "record field mismatch";
          Value.Make.str typ (List.map (fun (atom,t) ->
            atom, decode typedefs t (List.assoc (Domain.Atom.string_of_atom atom.it) actual)) fields)
      | _ -> fail ("unsupported observable type " ^ id.it))
  | _ -> fail "observation type mismatch"

let rec encode (value:Value.t) = match value.it with
  | BoolV b -> `Bool b
  | NumV n -> (match n with `Nat x | `Int x ->
      let s = Bigint.to_string x in
      match int_of_string_opt s with Some n -> `Int n | None -> `Intlit s)
  | TextV s -> `String s
  | TupleV xs | ListV xs -> `List (List.map encode xs)
  | OptV None -> `Null
  | OptV (Some x) -> encode x
  | StructV fields -> `Assoc (List.map (fun (a,v) -> Domain.Atom.string_of_atom a.it,encode v) fields)
  | _ -> fail "unsupported AL value in external request"

let input_context typedefs inputs json =
  let pairs = object_fields json in
  let expected = List.map (fun ((id:S.id),_) -> id.it) inputs in
  if List.sort String.compare expected <> List.sort String.compare (List.map fst pairs) then
    fail "property input fields mismatch";
  List.fold_left (fun ctx ((id:S.id), typ) ->
    Eval.Ctx.add_value ctx (id, []) (decode typedefs typ (List.assoc id.it pairs)))
    Eval.Ctx.empty inputs

let blocks_at blocks index =
  try List.nth blocks index with _ -> fail "AL block index mismatch"
let prem_at block index =
  try List.nth (fst block) index with _ -> fail "AL premise index mismatch"
let node_index id =
  let parts = String.split_on_char '.' id in
  try int_of_string (List.hd (List.rev parts)) with _ -> fail "invalid AL node ID"
let origin_index id =
  match String.split_on_char '.' id with
  | ["condition"; number] -> (try int_of_string number with _ -> fail "invalid condition origin")
  | _ -> fail "invalid condition origin"
let check_bool_prem ctx prem =
  match Eval.eval_prem ctx prem with
  | B.Ok ctx -> Some ctx
  | B.Unmatch _ -> None
  | B.Err _ -> fail "AL check evaluation error"

let request_inputs ctx (prem:S.prem) =
  match prem.it with
  | S.RulePr (_, notation, inputs) ->
      let args = Domain.Mixfix.args notation in
      let requested = List.mapi (fun index e -> index,e) args
        |> List.filter_map (fun (index,e) -> if List.mem index inputs then Some e else None) in
      `List (List.map (fun e -> encode (checked (Eval.eval_exp ctx e))) requested)
  | S.IfHoldPr (_, notation) | S.IfNotHoldPr (_, notation) ->
      `List (List.map (fun e -> encode (checked (Eval.eval_exp ctx e)))
        (Domain.Mixfix.args notation))
  | _ -> fail "external occurrence is not an AL relation"

let parse_occurrence blocks goal call =
  let id = text (field "id" call) in
  let origin = if id = "goal" then "goal" else
    if String.length id >= 5 && String.sub id 0 5 = "goal." then "goal" else
    if String.length id >= 10 && String.sub id 0 10 = "condition." then
      let parts = String.split_on_char '.' id in
      String.concat "." (List.filteri (fun i _ -> i < 2) parts)
    else fail "invalid occurrence ID" in
  let block = if origin = "goal" then goal else blocks_at blocks (origin_index origin) in
  let index = node_index (text (field "node_id" call)) in
  let prem = prem_at block index in
  let relation = text (field "relation" call) in
  let source_relation = match call with
    | `Assoc fields -> (match List.assoc_opt "source_relation" fields with
        | Some value -> text value | None -> relation)
    | _ -> fail "invalid external call" in
  let native_relation = match prem.it with
    | S.RulePr (rid,_,_) | S.IfHoldPr (rid,_) | S.IfNotHoldPr (rid,_) -> rid.it
    | _ -> fail "external occurrence is not an AL relation" in
  if native_relation <> source_relation then fail "AL occurrence relation mismatch";
  (block,index,prem)

let selector_type typedefs (prem:S.prem) selector =
  let arguments = match prem.it with
    | S.RulePr (_,notation,_) | S.IfHoldPr (_,notation) | S.IfNotHoldPr (_,notation) -> Domain.Mixfix.args notation
    | _ -> fail "selector requires a relation" in
  match String.split_on_char '.' selector with
  | slot :: fields when String.length slot > 1 && slot.[0] = '%' ->
      let number = try int_of_string (String.sub slot 1 (String.length slot - 1))
        with _ -> fail "invalid observation selector" in
      let root = try List.nth arguments number with _ -> fail "selector slot out of range" in
      let rec field_type typ field = match typ.it with
        | S.VarT (id,[]) -> (match Hashtbl.find_opt typedefs id.it with
            | Some {it=S.PlainT alias;_} -> field_type alias field
            | Some {it=S.StructT members;_} ->
                (match List.find_opt (fun (atom,_) ->
                  Domain.Atom.string_of_atom atom.it=field) members with
                 | Some (_,member_typ) -> member_typ
                 | None -> fail "selector field missing in record type")
            | _ -> fail "selector record type is unavailable")
        | _ -> fail "selector projects a non-record output" in
      let rec descend (expression:S.exp option) typ = function
        | [] -> typ
        | field :: rest ->
            (match expression with
             | Some {it=S.StrE members;_} ->
                 let child = List.find_opt (fun (atom,_) ->
                   Domain.Atom.string_of_atom atom.it = field) members in
                 (match child with Some (_,x) -> descend (Some x) (x.note $ x.at) rest
                  | None -> fail "selector field missing in AL output")
             | _ -> descend None (field_type typ field) rest) in
      descend (Some root) (root.note $ root.at) fields
  | _ -> fail "invalid observation selector"

let project_value (value:Value.t) fields =
  List.fold_left (fun (value:Value.t) field ->
    match value.it with
    | StructV members ->
        (match List.find_opt (fun (atom,_) ->
          Domain.Atom.string_of_atom atom.it = field) members with
         | Some (_,v) -> v | None -> fail "observation projection field missing")
    | _ -> fail "observation projection is not a record") value fields

let bind_observation typedefs ctx call prem entry =
  let observation = object_fields (field "observation" entry) in
  let selectors = List.map text (array (field "profile_selectors" call)) in
  if List.sort String.compare (List.map fst observation) <> List.sort String.compare selectors then
    fail "observation selectors mismatch";
  let decoded = List.map (fun selector ->
    selector, decode typedefs (selector_type typedefs prem selector)
      (List.assoc selector observation)) selectors in
  List.fold_left (fun ctx binding ->
    match field "selector" binding with
    | `Null -> ctx
    | `String selector ->
        let value = List.assoc selector decoded in
        let projected = List.map text (array (field "projection" binding)) in
        let value = project_value value projected in
        let name = text (field "name" binding) in
        Eval.Ctx.add_value ctx (name $ no_region, []) value
    | _ -> fail "invalid observation selector in binding")
    ctx (array (field "bindings" call))

let dependencies_ready statuses call =
  List.for_all (fun id ->
    try Hashtbl.find statuses (text id) = "success" with Not_found -> false)
    (array (field "dependencies" call))

let evaluate_lets ctx nodes =
  List.fold_left (fun ctx prem -> match (prem:S.prem).it with
    | S.LetPr _ -> (match Eval.eval_prem ctx prem with B.Ok next -> next | _ -> ctx)
    | _ -> ctx) ctx nodes

let prefix_lets ctx blocks goal call =
  let id = text (field "node_id" call) in
  let origin = text (field "id" call) in
  let block_index = if String.length origin >= 10 && String.sub origin 0 10 = "condition."
    then origin_index origin else List.length blocks in
  let ctx = List.fold_left (fun ctx index ->
    if index < block_index then evaluate_lets ctx (fst (blocks_at blocks index)) else ctx)
    ctx (List.init (List.length blocks) Fun.id) in
  let block = if block_index = List.length blocks then goal else blocks_at blocks block_index in
  let limit = node_index id in
  let nodes = List.filteri (fun i _ -> i < limit) (fst block) in
  evaluate_lets ctx nodes

let validate_entry typedefs blocks goal statuses ctx call entry =
  let id = text (field "id" call) in
  if text (field "occurrence_id" entry) <> id ||
     text (field "relation_id" entry) <> text (field "relation" call) then
    fail "trace occurrence identity mismatch";
  let _,_,prem = parse_occurrence blocks goal call in
  let ready = dependencies_ready statuses call in
  let expected = if ready then Some (request_inputs (prefix_lets ctx blocks goal call) prem)
    else None in
  let status = text (field "status" entry) in
  (match expected with
   | Some request ->
       if status = "blocked" || field "input" entry <> request then
         fail "recorded request input mismatch"
   | None ->
       if status <> "blocked" || field "input" entry <> `Null then
         fail "unavailable request must be blocked");
  let next = match status with
    | "success" -> bind_observation typedefs ctx call prem entry
    | "relation_failure" | "abort" | "execution_error" | "blocked" ->
        if object_fields (field "observation" entry) <> [] then
          fail "non-success occurrence has observations";
        ctx
    | _ -> fail "unknown observation status" in
  let inverted = match call with
    | `Assoc fields -> List.assoc_opt "invert" fields = Some (`Bool true)
    | _ -> false in
  let effective = if inverted then match status with
    | "success" -> "relation_failure"
    | "relation_failure" -> "success"
    | other -> other
    else status in
  Hashtbl.replace statuses id effective;
  next

let replay typedefs blocks goal ctx calls trace =
  let statuses = Hashtbl.create (List.length calls) in
  let ctx = List.fold_left2 (validate_entry typedefs blocks goal statuses)
    ctx (List.filteri (fun i _ -> i < List.length trace) calls) trace in
  (ctx,statuses)

let verdict value reason = json_obj ["verdict",`String value;"reason",`String reason]

let rec path_has_call (path:S.path) = match path.it with
  | S.RootP -> false
  | S.IdxP (parent,index) -> path_has_call parent || expression_has_call index
  | S.SliceP (parent,index,length) ->
      path_has_call parent || expression_has_call index || expression_has_call length
  | S.DotP (parent,_) -> path_has_call parent
and expression_has_call (expression:S.exp) =
  let any = List.exists expression_has_call in
  match expression.it with
  | S.CallE _ -> true
  | S.UnE (_,_,x) | S.UpCastE (_,x) | S.DownCastE (_,x)
  | S.SubE (x,_,_) | S.MatchE (x,_) | S.LenE x
  | S.DotE (x,_) | S.IterE (x,_) -> expression_has_call x
  | S.BinE (_,_,x,y) | S.CmpE (_,_,x,y) | S.ConsE (x,y)
  | S.CatE (x,y) | S.MemE (x,y) | S.IdxE (x,y) ->
      expression_has_call x || expression_has_call y
  | S.SliceE (x,y,z) -> any [x;y;z]
  | S.UpdE (x,path,y) -> any [x;y] || path_has_call path
  | S.TupleE xs | S.ListE xs -> any xs
  | S.CaseE notation -> any (Domain.Mixfix.args notation)
  | S.StrE members -> any (List.map snd members)
  | S.OptE possible -> Option.fold ~none:false ~some:expression_has_call possible
  | S.BoolE _ | S.NumE _ | S.TextE _ | S.VarE _ -> false

let rec prem_effect (prem:S.prem) =
  let expressions_have_call xs = List.exists expression_has_call xs in
  match prem.it with
  | S.RulePr (id,notation,_) | S.IfHoldPr (id,notation)
  | S.IfNotHoldPr (id,notation) ->
      (Some id.it, expressions_have_call (Domain.Mixfix.args notation))
  | S.IfPr x | S.DebugPr x -> (None,expression_has_call x)
  | S.LetPr (x,y) -> (None,expressions_have_call [x;y])
  | S.IterPr (inner,_) ->
      let rec inner_effect prem = match prem.it with
        | S.IterPr (nested,_) -> inner_effect nested
        | _ -> prem_effect prem in
      inner_effect inner

let audit_effects (spec_il:Lang.Il.spec) (spec:Lang.Al.spec) blocks goal plan =
  let calls = array (field "calls" plan) in
  let external_names = Hashtbl.create 32 in
  let external_nodes = Hashtbl.create 32 in
  List.iter (fun call ->
    Hashtbl.replace external_names (text (field "relation" call)) ();
    Hashtbl.replace external_nodes (text (field "node_id" call)) ();
    let _,_,source_prem = parse_occurrence blocks goal call in
    let source_negative = match source_prem.it with
      | S.IfNotHoldPr _ -> true | _ -> false in
    (match call with
    | `Assoc fields ->
        let inverted = List.assoc_opt "invert" fields = Some (`Bool true) in
        (match List.assoc_opt "source_relation" fields with
        | None ->
            if inverted <> source_negative then fail "external call negation mismatch"
        | Some source ->
            let source = text source and primitive = text (field "relation" call) in
            (match Property_document.delegate_target spec_il source primitive with
            | Some (_, helper_negative) when inverted = (helper_negative <> source_negative) -> ()
            | _ -> fail ("helper delegation does not match source relation " ^ source));
            if array (field "profile_selectors" call) <> [] then
              fail "delegated helper cannot observe primitive outputs")
    | _ -> fail "invalid external call")) calls;
  let definitions = Hashtbl.create 128 in
  List.iter (fun (definition:Lang.Al.def) -> match definition.it with
    | Lang.Al.ExternRelD (id,_,_,_) -> Hashtbl.replace external_names id.it ()
    | Lang.Al.RelD (id,_,_,groups,else_group,_) ->
        let group_parts = List.map (fun (group:Lang.Al.rulegroup) ->
          let _,(matches,outputs,initial),paths = group.it in
          (initial @ List.concat_map (fun (_,prems,_) -> prems) paths,
           matches @ outputs @ List.concat_map (fun (_,_,results) -> results) paths)) groups in
        let else_part = match else_group with
          | None -> ([],[])
          | Some group ->
              let _,(matches,outputs,initial),(_,path_prems,results) = group.it in
              (initial @ path_prems,matches @ outputs @ results) in
        Hashtbl.replace definitions id.it
          (List.concat_map fst group_parts @ fst else_part,
           List.concat_map snd group_parts @ snd else_part)
    | _ -> ()) spec;
  let visiting = Hashtbl.create 64 in
  let rec visit name =
    if Hashtbl.mem external_names name then
      fail ("dynamic external call under internal AL relation " ^ name);
    if not (Hashtbl.mem visiting name) then begin
      Hashtbl.replace visiting name ();
      let prems,expressions = match Hashtbl.find_opt definitions name with
        | Some xs -> xs | None -> fail ("internal AL relation is undefined: " ^ name) in
      if List.exists expression_has_call expressions then
        fail ("dynamic function call under internal AL relation " ^ name);
      List.iter (fun prem ->
        let next,has_function = prem_effect prem in
        if has_function then fail ("dynamic function call under internal AL relation " ^ name);
        Option.iter visit next) prems
    end in
  let check_prem node_id native =
    let relation,has_function = prem_effect native in
    if has_function then fail ("dynamic function call in runtime AL node " ^ node_id);
    match relation with
    | Some name when not (Hashtbl.mem external_nodes node_id) -> visit name
    | _ -> () in
  let check_node block node =
    let node_id = text (field "id" node) in
    check_prem node_id (prem_at block (node_index node_id)) in
  (* Match execution, not every logical premise in the contract. Internal
     condition relations are omitted by check_property and justified by the
     certified generator; their witnesses are not runtime inputs. *)
  List.iter (fun call ->
    let _,_,native = parse_occurrence blocks goal call in
    check_prem (text (field "node_id" call)) native) calls;
  (* evaluate_lets runs native condition lets, including proof-classified lets.
     Read these from AL so JSON node-list omissions cannot bypass the audit. *)
  List.iteri (fun block_index (prems,_) ->
    List.iteri (fun index (prem:S.prem) -> match prem.it with
      | S.LetPr _ ->
          check_prem ("condition." ^ string_of_int block_index ^ "." ^ string_of_int index) prem
      | _ -> ()) prems) blocks;
  List.iter (fun block ->
    let native=blocks_at blocks (origin_index (text (field "origin" block))) in
    List.iter (check_node native) (array (field "nodes" block)))
    (array (field "checks" plan));
  (* eval_goal executes every native goal premise, regardless of plan labels. *)
  List.iteri (fun index prem -> check_prem ("goal." ^ string_of_int index) prem) (fst goal)

let check_property plan blocks goal calls ctx statuses =
  let call_status id =
    try Hashtbl.find statuses id with Not_found -> fail "missing occurrence status" in
  let statuses_all = List.map (fun call -> call_status (text (field "id" call))) calls in
  if List.exists ((=) "execution_error") statuses_all then
    verdict "error" "external_execution_error"
  else if List.exists ((=) "abort") statuses_all then
    verdict "error" "external_abort"
  else if List.exists ((=) "relation_failure") statuses_all then
    verdict "fail" "external_relation_failure"
  else if List.exists ((=) "blocked") statuses_all then
    verdict "fail" "blocked_external_dependency"
  else
    let ctx = List.fold_left (fun ctx block -> evaluate_lets ctx (fst block)) ctx blocks in
    let checks = array (field "checks" plan) in
    let observed_ok = List.for_all (fun block ->
      let index = origin_index (text (field "origin" block)) in
      let native = blocks_at blocks index in
      List.for_all (fun node ->
        let premise = prem_at native (node_index (text (field "id" node))) in
        match premise.it with
        | S.IfPr _ -> Option.is_some (check_bool_prem ctx premise)
        | S.LetPr _ -> true
        | S.RulePr _ | S.IfHoldPr _ -> fail "relation in observed guard block"
        | _ -> fail "unsupported observed AL premise")
        (array (field "nodes" block))) checks in
    if not observed_ok then verdict "fail" "observed_condition_false"
    else
      let external_nodes = Hashtbl.create (List.length calls) in
      List.iter (fun call -> Hashtbl.replace external_nodes
        (text (field "node_id" call)) (text (field "id" call))) calls;
      let rec eval_goal ctx index = function
        | [] -> verdict "pass" "goal_true"
        | prem :: rest ->
            let id = "goal." ^ string_of_int index in
            let next = match Hashtbl.find_opt external_nodes id with
              | Some occurrence -> if call_status occurrence = "success" then Some ctx
                else None
              | None -> check_bool_prem ctx prem in
            match next with
            | Some next -> eval_goal next (index+1) rest
            | None -> verdict "fail" "goal_false" in
      eval_goal ctx 0 (fst goal)

let main () =
  let specs = ref [] and property = ref "" and name = ref "" and plan_path = ref "" in
  Arg.parse ["--spec",Arg.String(fun x -> specs := !specs @ [x]),"SpecTec source";
    "--property",Arg.Set_string property,"Property source";
    "--name",Arg.Set_string name,"Property name";
    "--plan",Arg.Set_string plan_path,"Certified plan"]
    (fun _ -> fail "unexpected argument") "property_exec --spec FILE --property FILE --name NAME --plan FILE";
  if !specs = [] || !property = "" || !name = "" || !plan_path = "" then fail "missing executor argument";
  let request = J.from_string (input_line stdin) in
  unique_json request;
  let plan = J.from_file !plan_path in
  unique_json plan;
  if field "schema_version" plan <> `Int 2 || text (field "engine" plan) <> "spectec-al" then
    fail "property plan schema 2 required";
  if field "plan_id" request <> field "plan_id" plan then fail "plan identity mismatch";
  let inputs, blocks, goal, spec_il, spec_al = parse_property !specs !property !name in
  let typedefs = types spec_il in
  (match Eval.init ~cache:false ~det:false ~guard:true spec_al with
   | Ok () -> () | Error d -> fail (report d));
  let mode = text (field "mode" request) in
  let trace = array (field "trace" request) in
  let calls = array (field "calls" plan) in
  if List.length trace > List.length calls then fail "too many trace entries";
  let result = if mode = "audit" then begin
      audit_effects spec_il spec_al blocks goal plan;
      json_obj ["valid",json_bool true]
    end else
  let ctx = input_context typedefs inputs (field "input" request) in
  match mode with
    | "request" ->
        let index = match field "index" request with `Int i -> i | _ -> fail "request index must be integer" in
        if index < 0 || index >= List.length calls || List.length trace <> index then
          fail "request prefix length mismatch";
        let ctx,statuses = replay typedefs blocks goal ctx calls trace in
        let call = List.nth calls index in
        if dependencies_ready statuses call then
          let _,_,prem = parse_occurrence blocks goal call in
          json_obj ["ready",json_bool true;
            "input",request_inputs (prefix_lets ctx blocks goal call) prem]
        else json_obj ["ready",json_bool false]
    | "validate" ->
        let _ = replay typedefs blocks goal ctx calls trace in
        json_obj ["valid",json_bool true]
    | "check" ->
        if List.length trace <> List.length calls then fail "incomplete trace";
        let ctx,statuses = replay typedefs blocks goal ctx calls trace in
        check_property plan blocks goal calls ctx statuses
    | _ -> fail "unsupported native executor mode" in
  print_endline (J.to_string result)

let () = try main () with
  | Failure message -> prerr_endline message; exit 1
  | Yojson.Json_error message -> prerr_endline message; exit 1
  | Frontend.Error.ParseError d -> prerr_endline (report d); exit 1
  | Run.ExternError failure ->
      prerr_endline (report (Run.diagnostic_of_failure failure)); exit 1
