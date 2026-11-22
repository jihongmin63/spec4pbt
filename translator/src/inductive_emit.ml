open Coq_ir

exception Unsupported of string

type relation = {
  name : string;
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
  | Constructor (name, arguments) | Primitive (name, arguments) ->
      Render.apply name (List.map (render_expression environment) arguments)
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
  String.init (String.length bytes / 2) (fun i ->
    Char.chr (int_of_string ("0x" ^ String.sub bytes (2 * i) 2)))

let pattern_binders scrutinee pattern =
  if String.starts_with ~prefix:"Some " pattern then
    match scrutinee.typ with
    | Option inner ->
        let raw = String.trim (String.sub pattern 5 (String.length pattern - 5)) in
        if String.contains raw ' ' then
          raise (Unsupported ("unsupported nested option pattern " ^ pattern));
        [{name = decoded_identifier raw; typ = inner}, raw]
    | _ -> raise (Unsupported ("Some pattern on non-option expression"))
  else if String.starts_with ~prefix:"v_" pattern then
    [{name = decoded_identifier pattern; typ = scrutinee.typ}, pattern]
  else if identifiers pattern <> [] then
    raise (Unsupported ("pattern with nested binders is not supported: " ^ pattern))
  else []

let rec expression_identifiers value =
  match value.term with
  | Variable name -> [Render.identifier name]
  | Literal code -> identifiers code
  | Constructor (_, arguments) | Primitive (_, arguments) | Tuple arguments ->
      List.concat_map expression_identifiers arguments
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
            (pattern_binders value pattern) in
        List.filter (fun name -> not (List.mem name bound)) (free_action branch)) branches
  | Local (binding, value, right) ->
      expression_identifiers value @ without_binding binding (free_action right)
  | Traverse (binding, values, right) ->
      expression_identifiers values @ without_binding binding (free_action right)
  | Primitive_action (_, arguments) -> List.concat_map expression_identifiers arguments

let relation name arguments output = {name; arguments; output; constructors = []}

