open Coq_ir

exception Unsupported of string

type relation = {
  name : string;
  parameters : string list;
  extra_quantifiers : (string * string) list;
  arguments : string list;
  output : typ;
  mutable constructors : string list;
}

type environment = (binding * string) list

type path = {
  relation : relation;
  indices : string list;
  state : string;
  variables : (string * string) list;
  premises : string list;
  environment : environment;
}

let parenthesize s = "(" ^ s ^ ")"
let applied name values = String.concat " " (name :: List.map parenthesize values)
let type_string = Emit_data.render_type
let variable (binding : binding) = Render.identifier binding.name

(* Each listed P4 helper reduces to Return, Unmatched, or Raise after its
   arguments are supplied. A new helper needs an explicit review here; Fresh
   is handled separately below because it changes State. *)
let terminal_p4_helpers = [
  "sum_nat"; "max_nat"; "min_nat"; "sum_int"; "max_int"; "min_int";
  "text_to_int"; "int_to_text"; "split_text"; "strip_prefix";
  "strip_suffix"; "strip_all_whitespace"; "rev_"; "concat_";
  "partition_"; "assoc_"; "sort_"; "distinct_";
  "intersect_set"; "union_set"; "unions_set"; "diff_set";
  "sub_set"; "eq_set"; "find_map"; "find_maps"; "add_map";
  "adds_map"; "update_map"; "print_"; "bitstr_to_int";
  "int_to_bitstr"; "bits_to_int_unsigned"; "bits_to_int_signed";
  "int_to_bits_unsigned"; "int_to_bits_signed"; "pow2"; "shl";
  "shr"; "shr_arith"; "bneg"; "band"; "bxor"; "bor";
  "bitacc"; "bitacc_replace";
]

let terminal_primitive profile helper =
  (profile = "p4" || profile = "wasm") &&
  (List.exists (fun name ->
     String.starts_with ~prefix:("(@P4." ^ name ^ " Call") helper)
     terminal_p4_helpers ||
   (profile = "wasm" && String.starts_with ~prefix:"(WasmScalar.lift " helper))

let string_of_path path outcome final =
  applied path.relation.name (path.indices @ [outcome; final])

let counter = ref 0
let fresh prefix = incr counter; prefix ^ string_of_int !counter

let add_variable path name typ =
  {path with variables = path.variables @ [name, typ]}

let add_premise path premise =
  {path with premises = path.premises @ [premise]}

let add_environment path (binding : binding) value =
  {path with environment = (binding, value) ::
      List.filter (fun ((old : binding), _) -> old.name <> binding.name) path.environment}

let emit path outcome final =
  let binders = String.concat " " (List.map (fun (name, typ) ->
      "(" ^ name ^ " : " ^ typ ^ ")") path.variables) in
  let premises = String.concat "" (List.map (fun p -> p ^ " -> ") path.premises) in
  let constructor = "| " ^ fresh "direct_case_" ^ " : forall " ^ binders ^ ", " ^
      premises ^ string_of_path path outcome final in
  path.relation.constructors <- path.relation.constructors @ [constructor]

let is_word = function
  | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true
  | _ -> false

let identifiers source =
  let length = String.length source in
  let rec collect index quoted found =
    if index >= length then found else
    let c = source.[index] in
    if c = '"' then collect (index + 1) (not quoted) found
    else if quoted && c = '\\' && index + 1 < length then
      collect (index + 2) quoted found
    else if not quoted && is_word c then
      let stop = ref (index + 1) in
      while !stop < length && is_word source.[!stop] do incr stop done;
      let token = String.sub source index (!stop - index) in
      collect !stop quoted (if String.starts_with ~prefix:"v_" token then token :: found else found)
    else collect (index + 1) quoted found
  in
  collect 0 false []

(* AL lowering sometimes embeds a Coq term in Literal. Replace only complete
   generated identifiers, and never substitute inside a string literal. *)
let substitute (environment : environment) source =
  let table = List.map (fun ((binding : binding), value) -> variable binding, parenthesize value) environment in
  let buffer = Buffer.create (String.length source) in
  let length = String.length source in
  let rec visit index quoted =
    if index < length then
      let c = source.[index] in
      if c = '"' then (Buffer.add_char buffer c; visit (index + 1) (not quoted))
      else if quoted && c = '\\' && index + 1 < length then (
        Buffer.add_char buffer c; Buffer.add_char buffer source.[index + 1];
        visit (index + 2) quoted)
      else if not quoted && is_word c then (
        let stop = ref (index + 1) in
        while !stop < length && is_word source.[!stop] do incr stop done;
        let token = String.sub source index (!stop - index) in
        Buffer.add_string buffer (match List.assoc_opt token table with Some v -> v | None -> token);
        visit !stop quoted)
      else (Buffer.add_char buffer c; visit (index + 1) quoted)
  in
  visit 0 false;
  Buffer.contents buffer

let without_names names environment =
  List.filter (fun ((binding : binding), _) ->
    not (List.mem (variable binding) names)) environment

let rec render_expression environment value =
  match value.term with
  | Variable name ->
      (match List.find_opt (fun ((binding : binding), _) -> binding.name = name) environment with
       | Some (_, replacement) -> parenthesize replacement
       | None -> Render.identifier name)
  | Literal code -> substitute environment code
  | Constructor (name, arguments) ->
      Render.apply name (List.map (render_expression environment) arguments)
  | Primitive (name, arguments) ->
      Render.apply (substitute environment name)
        (List.map (render_expression environment) arguments)
  | Tuple values -> Render.tuple (List.map (render_expression environment) values)
  | Projection (record, name) -> Render.apply name [render_expression environment record]
  | Lambda (bindings, body) ->
      let bound = List.map variable bindings in
      let scoped = without_names bound environment in
      Render.par ("fun " ^ String.concat " " (List.map Render.binding bindings) ^
                  " => " ^ render_expression scoped body)
  | Apply (fn, arguments) ->
      Render.apply (render_expression environment fn)
        (List.map (render_expression environment) arguments)
  | Match_term (scrutinee, branches) ->
      Render.par ("match " ^ render_expression environment scrutinee ^ " with " ^
        String.concat " " (List.map (fun (pattern, branch) ->
          let scoped = without_names (identifiers pattern) environment in
          "| " ^ pattern ^ " => " ^ render_expression scoped branch) branches) ^ " end")
  | Function name -> Render.reference_constructor name

let expression path value = render_expression path.environment value
let error path err = emit path ("Error " ^ parenthesize err) path.state

let decoded_identifier raw =
  if not (String.starts_with ~prefix:"v_" raw) then
    raise (Unsupported ("unsupported pattern binder " ^ raw));
  let bytes = String.sub raw 2 (String.length raw - 2) in
  if String.length bytes mod 2 <> 0 then
    raise (Unsupported ("malformed pattern binder " ^ raw));
  try String.init (String.length bytes / 2) (fun i ->
    Char.chr (int_of_string ("0x" ^ String.sub bytes (2 * i) 2)))
  with Failure _ -> raise (Unsupported ("malformed pattern binder " ^ raw))

let rec pattern_literal_types action =
  let rec from_expression value =
    let direct = match value.term with
      | Literal code when String.starts_with ~prefix:"v_" code &&
          identifiers code = [code] -> [code, value.typ]
      | _ -> [] in
    direct @ (match value.term with
      | Constructor (_, xs) | Primitive (_, xs) | Tuple xs ->
          List.concat_map from_expression xs
      | Projection (x, _) -> from_expression x
      | Lambda (_, x) -> from_expression x
      | Apply (f, xs) -> from_expression f @ List.concat_map from_expression xs
      | Match_term (x, branches) -> from_expression x @
          List.concat_map (fun (_, branch) -> from_expression branch) branches
      | Variable _ | Literal _ | Function _ -> []) in
  let children = match action.node with
    | Return value | Guard value -> from_expression value
    | Invoke call -> List.concat_map from_expression call.arguments
    | Bind (_, left, right) -> pattern_literal_types left @ pattern_literal_types right
    | Alternatives actions -> List.concat_map pattern_literal_types actions
    | Negate inner -> pattern_literal_types inner
    | Match (value, branches) -> from_expression value @
        List.concat_map (fun (_, branch) -> pattern_literal_types branch) branches
    | Local (_, value, right) -> from_expression value @ pattern_literal_types right
    | Traverse (_, values, right) -> from_expression values @ pattern_literal_types right
    | Primitive_action (_, args) -> List.concat_map from_expression args
    | Unmatch | Error _ | Fresh | Choose _ -> [] in
  children

let pattern_binders scrutinee pattern branch =
  let names = List.sort_uniq String.compare (identifiers pattern) in
  let inferred = pattern_literal_types branch in
  List.map (fun raw ->
    let typ = match List.assoc_opt raw inferred with
      | Some typ -> typ
      | None when names = [raw] ->
          (match scrutinee.typ with Option typ when String.starts_with ~prefix:"Some " pattern -> typ
           | typ -> typ)
      | None -> raise (Unsupported ("cannot infer pattern binder type: " ^ raw ^ " in " ^ pattern)) in
    {name = decoded_identifier raw; typ}, raw) names

let rec expression_identifiers value =
  match value.term with
  | Variable name -> [Render.identifier name]
  | Literal code -> identifiers code
  | Constructor (_, arguments) | Tuple arguments ->
      List.concat_map expression_identifiers arguments
  | Primitive (name, arguments) ->
      identifiers name @ List.concat_map expression_identifiers arguments
  | Projection (record, _) -> expression_identifiers record
  | Lambda (bindings, body) ->
      let bound = List.map variable bindings in
      List.filter (fun name -> not (List.mem name bound)) (expression_identifiers body)
  | Apply (fn, arguments) ->
      expression_identifiers fn @ List.concat_map expression_identifiers arguments
  | Match_term (scrutinee, branches) ->
      expression_identifiers scrutinee @
      List.concat_map (fun (pattern, branch) ->
        let bound = identifiers pattern in
        List.filter (fun name -> not (List.mem name bound))
          (expression_identifiers branch)) branches
  | Function _ -> []
let without_binding binding names =
  List.filter ((<>) (variable binding)) names

let rec free_action action =
  match action.node with
  | Return value | Guard value -> expression_identifiers value
  | Invoke call -> List.concat_map expression_identifiers call.arguments
  | Bind (binding, left, right) ->
      free_action left @ without_binding binding (free_action right)
  | Alternatives actions -> List.concat_map free_action actions
  | Unmatch | Error _ | Fresh | Choose _ -> []
  | Negate inner -> free_action inner
  | Match (value, branches) ->
      expression_identifiers value @
      List.concat_map (fun (pattern, branch) ->
        let bound = List.map (fun (binding, _) -> variable binding)
            (pattern_binders value pattern branch) in
        List.filter (fun name -> not (List.mem name bound)) (free_action branch)) branches
  | Local (binding, value, right) ->
      expression_identifiers value @ without_binding binding (free_action right)
  | Traverse (binding, values, right) ->
      expression_identifiers values @ without_binding binding (free_action right)
  | Primitive_action (helper, arguments) ->
      identifiers helper @ List.concat_map expression_identifiers arguments

let relation name parameters arguments output =
  {name; parameters; extra_quantifiers = []; arguments; output; constructors = []}

let parameter_binders parameters =
  List.map (fun name -> name, "Set") parameters @
  List.map (fun name -> "ops_" ^ name, "ValueOps@{Set} " ^ name) parameters

let parameter_values parameters = parameters @ List.map (fun name -> "ops_" ^ name) parameters

let render ctx bodies =
  let current_location = ref Util.Source.no_region in
  try
    counter := 0;
    let known = List.map (fun (body : body) -> body.call_name) bodies in
    let all = ref [] in
    let register value = all := !all @ [value]; value in
    let apply_relation = register
      { (relation "R_apply" []
           ["FunctionRef apply_input apply_output"; "apply_input"; "State"]
           (Type_parameter "apply_output")) with
        extra_quantifiers = ["apply_input", "Set"; "apply_output", "Set"] } in
    let reference_names = List.filter_map (function
      | `Assoc fields -> (match List.assoc_opt "global_declaration" fields with
          | Some (`String name) -> Some name | _ -> None)
      | _ -> None) (Context.function_reference_inventory ctx) |> List.sort_uniq String.compare in
    List.iter (fun target_name ->
      match List.find_opt (fun (body : body) -> body.call_name = target_name) bodies with
      | None -> ()
      | Some target ->
          let declaration = Context.String_map.find target_name ctx.Context.by_generated_name in
          let signature = Option.get declaration.signature in
          let parameters = List.map (fun p ->
            Data.parameter_name ctx p.Util.Source.it) signature.type_parameters in
          let parameter_values = parameter_values parameters in
          let inputs = List.map (fun (b : binding) -> type_string b.typ) target.parameters in
          let input_type = type_string (Product (List.map (fun (b : binding) -> b.typ) target.parameters)) in
          let result_type = type_string target.result in
          let args = List.map variable target.parameters in
          let start = fresh "apply_start_" in
          let outcome = fresh "apply_outcome_" in
          let final = fresh "apply_final_" in
          let reference = applied (Render.reference_constructor target_name) parameter_values in
          let path = {relation = apply_relation;
            indices = [input_type; result_type; reference; Render.tuple args; start];
            state = start;
            variables = parameter_binders parameters @
              List.map2 (fun name typ -> name, typ) args inputs @
              [start, "State"; outcome, "Outcome " ^ parenthesize result_type; final, "State"];
            premises = [applied (target_name ^ "_execute")
              (parameter_values @ args @ [start; outcome; final])];
            environment = []} in
          emit path outcome final) reference_names;
    let compiler_body (body : body) =
      let declaration = Context.String_map.find body.call_name ctx.Context.by_generated_name in
      current_location := declaration.location;
      let signature = Option.get declaration.signature in
      let parameters = List.map (fun p ->
        Data.parameter_name ctx p.Util.Source.it) signature.type_parameters in
      let parameter_values = parameter_values parameters in
      let parameter_binders = parameter_binders parameters in
      let clauses = match body.action.node with
        | Alternatives [] -> [{result = body.result; node = Unmatch}]
        | Alternatives xs -> xs
        | _ -> [body.action] in
      let count = List.length clauses in
      let inputs = body.parameters in
      let input_types = List.map (fun (b : binding) -> type_string b.typ) inputs in
      let make_clause index =
        let suffix = if index = 1 then "_execute" else "_continue_from_" ^ string_of_int index in
        register (relation (body.call_name ^ suffix) parameters (input_types @ ["State"]) body.result) in
      let clause_relations = Array.init count (fun i -> make_clause (i + 1)) in
      let call_index = ref 0 in
      let traverse_index = ref 0 in
      let rec compile index live action path success miss fail =
        match action.node with
        | Return value -> success path (expression path value)
        | Unmatch -> miss path
        | Error err -> fail path err
        | Fresh ->
            let value = "next_fresh " ^ parenthesize path.state in
            let next = "{| next_fresh := S " ^ parenthesize value ^ " |}" in
            success {path with state = next} value
        | Guard condition ->
            let value = expression path condition in
            success (add_premise path (value ^ " = true")) "tt";
            miss (add_premise path (value ^ " = false"))
        | Local (binding, value, right) ->
            compile index live right (add_environment path binding (expression path value)) success miss fail
        | Bind (binding, left, right) ->
            let needed_after_left = without_binding binding (free_action right) @ live in
            compile index needed_after_left left path
              (fun path value -> compile index live right (add_environment path binding value) success miss fail)
              miss fail
        | Alternatives actions ->
            let alternatives = function
              | [] -> miss path
              | head :: tail ->
                  compile index (live @ List.concat_map free_action tail) head path success
                    (fun path -> if tail = [] then miss path else
                       let rec next path = function
                         | [] -> miss path
                         | x :: xs -> compile index
                             (live @ List.concat_map free_action xs)
                             x path success
                             (fun path -> next path xs) fail in
                       next path tail)
                    fail in
            alternatives actions
        | Choose chosen_type ->
            let chosen = fresh "chosen_" in
            success (add_variable path chosen (type_string chosen_type)) chosen
        | Negate inner ->
            compile index live inner path
              (fun path _ -> miss path)
              (fun path -> success path "tt") fail
        | Invoke call ->
            if call.target <> "#apply" && not (List.mem call.target known) then
              raise (Unsupported (body.call_name ^ ": unknown call target " ^ call.target));
            incr call_index;
            let after_name = Printf.sprintf "%s_after_call_%d_at_%d"
                body.call_name !call_index index in
            let captured = List.rev (List.filter (fun ((binding : binding), _) ->
              List.mem (variable binding) live ||
              (index < count && List.exists (fun (input : binding) -> input.name = binding.name) inputs))
                path.environment) in
            let after = register (relation after_name parameters
                (List.map (fun ((b : binding), _) -> type_string b.typ) captured @
                 ["Outcome " ^ parenthesize (type_string call.result); "State"])
                path.relation.output) in
            let captured_values = List.map snd captured in
            let formal = List.map (fun (b, _) -> (b, variable b)) captured in
            let formal_values = List.map snd formal in
            let call_result = fresh "call_outcome_" in
            let call_state = fresh "call_state_" in
            let outcome = fresh "outcome_" in
            let final = fresh "final_" in
            let args = List.map (expression path) call.arguments in
            let call_parameters = List.map type_string call.type_arguments @
              List.map Emit_data.ops_expr call.type_arguments in
            let target = if call.target = "#apply" then
              match call.arguments with
              | [_reference; input] -> applied apply_relation.name
                  ([type_string input.typ; type_string call.result] @ args @
                   [path.state; call_result; call_state])
              | _ -> raise (Unsupported (body.call_name ^ ": malformed higher-order call"))
              else applied (call.target ^ "_execute")
                (call_parameters @ args @ [path.state; call_result; call_state]) in
            let after_call = applied after.name
                (parameter_values @ captured_values @ [call_result; call_state; outcome; final]) in
            let parent = path |> fun p -> add_variable p call_result
                  ("Outcome " ^ parenthesize (type_string call.result)) in
            let parent = add_variable parent call_state "State" in
            let parent = add_variable parent outcome
                ("Outcome " ^ parenthesize (type_string path.relation.output)) in
            let parent = add_variable parent final "State" in
            emit (parent |> fun p -> add_premise (add_premise p target) after_call) outcome final;
            let make_after call_outcome state extra =
              {relation = after; indices = parameter_values @ formal_values @ [call_outcome; state];
               state; variables = parameter_binders @
                 List.map (fun ((b : binding), _) -> variable b, type_string b.typ) formal @ extra;
               premises = []; environment = formal} in
            let result_name = fresh "value_" in
            let success_path = make_after ("Success " ^ result_name) call_state
                [result_name, type_string call.result; call_state, "State"] in
            success success_path result_name;
            let miss_path = make_after "Unmatch" call_state [call_state, "State"] in
            miss miss_path;
            let err_name = fresh "error_" in
            let error_path = make_after ("Error " ^ err_name) call_state
                [err_name, "ExecutionError"; call_state, "State"] in
            fail error_path err_name
        | Match (scrutinee, branches) ->
            let value = expression path scrutinee in
            let previous = ref [] in
            List.iter (fun (pattern, branch) ->
              let branch_path = List.fold_left (fun path prior ->
                add_premise path ("(match " ^ value ^ " with | " ^ prior ^
                  " => false | _ => true end) = true")) path !previous in
              let binders = pattern_binders scrutinee pattern branch in
              let branch_path = List.fold_left (fun path ((binding : binding), raw) ->
                add_environment (add_variable path raw (type_string binding.typ)) binding raw)
                  branch_path binders in
              let branch_path = if pattern = "_" then branch_path else
                add_premise branch_path (value ^ " = " ^ parenthesize pattern) in
              compile index live branch branch_path success miss fail;
              previous := !previous @ [pattern]) branches
        | Traverse _ -> raise (Unsupported (body.call_name ^ ": Traverse direct rule is not supported"))
        | Primitive_action ("(@P4.fresh_typeId Call)", []) when ctx.Context.profile.name = "p4" ->
            let number = "next_fresh " ^ parenthesize path.state in
            let value = "String.append \"FRESH__\" (print_nat " ^ parenthesize number ^ ")" in
            let next = "{| next_fresh := S " ^ parenthesize number ^ " |}" in
            success {path with state = next} value
        | Primitive_action (helper, arguments) ->
            if not (terminal_primitive ctx.Context.profile.name helper) then
              raise (Unsupported (body.call_name ^
                ": primitive helper has no terminal Action contract: " ^ helper));
            let primitive = Render.apply (substitute path.environment helper)
              (List.map (expression path) arguments) in
            let result_type = type_string action.result in
            let value = fresh "primitive_value_" in
            let success_path = add_variable path value result_type in
            success (add_premise success_path
              (primitive ^ " = (@Return Call " ^ result_type ^ " " ^ value ^ ")")) value;
            miss (add_premise path
              (primitive ^ " = (@Unmatched Call " ^ result_type ^ ")"));
            let err = fresh "primitive_error_" in
            let fail_path = add_variable path err "ExecutionError" in
            fail (add_premise fail_path
              (primitive ^ " = (@Raise Call " ^ result_type ^ " " ^ err ^ ")")) err in
      Array.iteri (fun i clause ->
        let index = i + 1 in
        call_index := 0;
        traverse_index := 0;
        let relation = clause_relations.(i) in
        let initial_state = fresh "start_" in
        let indices = parameter_values @ List.map variable inputs @ [initial_state] in
        let variables = parameter_binders @
            List.map (fun (b : binding) -> variable b, type_string b.typ) inputs @
            [initial_state, "State"] in
        let environment = List.map (fun b -> b, variable b) inputs in
        let path = {relation; indices; state = initial_state; variables;
                    premises = []; environment} in
        let success path value = emit path ("Success " ^ parenthesize value) path.state in
        let miss path =
          if index = count then emit path "Unmatch" path.state
          else let outcome = fresh "outcome_" and final = fresh "final_" in
            let path = add_variable (add_variable path outcome
                ("Outcome " ^ parenthesize (type_string body.result))) final "State" in
            let next = applied clause_relations.(index).name
                (parameter_values @ List.map variable inputs @ [path.state; outcome; final]) in
            emit (add_premise path next) outcome final in
        compile index [] clause path success miss error)
        (Array.of_list clauses);
      () in
    List.iter compiler_body bodies;
    let render_relation first item =
      (if first then "Inductive " else "with ") ^ item.name ^ " : " ^
      (if item.parameters = [] && item.extra_quantifiers = [] then "" else
         "forall " ^ String.concat " " (List.map (fun (name, typ) ->
           "(" ^ name ^ " : " ^ typ ^ ")")
             (item.extra_quantifiers @ parameter_binders item.parameters)) ^ ", ") ^
      String.concat " -> " (item.arguments @
        ["Outcome " ^ parenthesize (type_string item.output); "State"; "Prop"]) ^
      " :=\n" ^ String.concat "\n" item.constructors in
    let relations = Array.of_list !all in
    let count = Array.length relations in
    let by_name = Hashtbl.create count in
    Array.iteri (fun index item -> Hashtbl.add by_name item.name index) relations;
    let dependencies = Array.init count (fun index ->
      let found = Hashtbl.create 8 in
      let scan source =
        let length = String.length source in
        let rec loop start =
          if start < length then
            if is_word source.[start] then (
              let stop = ref (start + 1) in
              while !stop < length && is_word source.[!stop] do incr stop done;
              let token = String.sub source start (!stop - start) in
              (match Hashtbl.find_opt by_name token with
               | Some dependency when dependency <> index ->
                   Hashtbl.replace found dependency ()
               | _ -> ());
              loop !stop)
            else loop (start + 1) in
        loop 0 in
      List.iter scan relations.(index).constructors;
      Hashtbl.fold (fun dependency () result -> dependency :: result) found []
      |> List.sort compare) in
    let visit_number = ref 0 in
    let visit = Array.make count (-1) in
    let lowlink = Array.make count (-1) in
    let in_stack = Array.make count false in
    let stack = ref [] in
    let components = ref [] in
    let rec strong index =
      visit.(index) <- !visit_number;
      lowlink.(index) <- !visit_number;
      incr visit_number;
      stack := index :: !stack;
      in_stack.(index) <- true;
      List.iter (fun dependency ->
        if visit.(dependency) = -1 then (
          strong dependency;
          lowlink.(index) <- min lowlink.(index) lowlink.(dependency))
        else if in_stack.(dependency) then
          lowlink.(index) <- min lowlink.(index) visit.(dependency))
        dependencies.(index);
      if lowlink.(index) = visit.(index) then (
        let rec pop members =
          match !stack with
          | [] -> assert false
          | head :: rest ->
              stack := rest;
              in_stack.(head) <- false;
              let members = head :: members in
              if head = index then members else pop members in
        components := pop [] :: !components) in
    for index = 0 to count - 1 do
      if visit.(index) = -1 then strong index
    done;
    let blocks = List.rev !components |> List.map (fun members ->
      let members = List.sort compare members in
      String.concat "\n" (List.mapi (fun ordinal index ->
        render_relation (ordinal = 0) relations.(index)) members) ^ ".") in
    let rec chunk current size result = function
      | [] -> List.rev (if current = [] then result else
          (String.concat "\n\n" (List.rev current) ^ "\n") :: result)
      | block :: rest when size + String.length block > 750_000 && current <> [] ->
          chunk [block] (String.length block) ((String.concat "\n\n" (List.rev current) ^ "\n") :: result) rest
      | block :: rest -> chunk (block :: current) (size + String.length block) result rest in
    Ok (chunk [] 0 [] blocks)
  with Unsupported reason ->
    Error [{stage = "inductive"; location = !current_location;
            construct = "Action"; reason}]
