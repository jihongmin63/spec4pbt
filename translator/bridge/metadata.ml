(** Observation metadata and JSON transport for the unmodified P4-SpecTec
    translator.  This helper elaborates types and relation roles through Pass;
    it never translates a rule, premise, expression, or execution semantics. *)
open Util.Source
module S = Lang.Il

exception Invalid_metadata of string
let fail message = raise (Invalid_metadata message)
let string value = `String value
let object_ fields = `Assoc fields
let array values = `List values

let contains text fragment =
  let rec loop index =
    index + String.length fragment <= String.length text &&
    (String.sub text index (String.length fragment) = fragment || loop (index + 1)) in
  loop 0

let quote name =
  if name = "" || contains name "»" ||
     String.exists (fun c -> Char.code c < 32 || Char.code c = 127) name then
    fail ("unrepresentable Lean identifier: " ^ name);
  "«" ^ name ^ "»"

let letter = function 'a'..'z' | 'A'..'Z' | '_' -> true | _ -> false
let digit = function '0'..'9' -> true | _ -> false
let ordinary name =
  name <> "" && letter name.[0] &&
  String.for_all (fun c -> letter c || digit c || c = '\'') name

let qualified label name =
  let parts = String.split_on_char '.' name in
  if not (List.for_all ordinary parts) || List.exists ((=) "_") parts then
    fail (label ^ ": expected an ordinary qualified Lean identifier");
  String.concat "." (List.map quote parts)

let fields label required = function
  | `Assoc items ->
      let keys = List.map fst items in
      if List.length (List.sort_uniq String.compare keys) <> List.length keys then
        fail (label ^ ": duplicate object field");
      if List.sort String.compare keys <> List.sort String.compare required then
        fail (label ^ ": unexpected or missing object fields");
      items
  | _ -> fail (label ^ ": expected an object")

let text label = function
  | `String value when value <> "" -> value
  | _ -> fail (label ^ ": expected a nonempty string")

type typ =
  | Primitive of string
  | Named of string * typ list
  | Sequence of typ
  | Optional of typ
  | Tuple of typ list
  | Function

type definition = { parameters : string list; body : body }
and body = Alias of typ | Record of (string * typ) list | Variant of typ list | External
type relation = { name : string; inputs : int list; arguments : typ list }
type observation = { relation_name : string; selectors : string list }

let rec convert (typ : S.typ) = match typ.it with
  | BoolT -> Primitive "bool"
  | NumT `NatT -> Primitive "nat"
  | NumT `IntT -> Primitive "int"
  | TextT -> Primitive "text"
  | VarT (id, args) -> Named (id.it, List.map (fun (arg : S.targ) -> convert (arg.it $ arg.at)) args)
  | IterT (element, List) -> Sequence (convert element)
  | IterT (element, Opt) -> Optional (convert element)
  | TupleT (_ :: _ :: _ as elements) -> Tuple (List.map convert elements)
  | FuncT _ -> Function
  | _ -> fail ("unsupported observation type: " ^ S.Print.string_of_typ typ)

let field_name (atom : S.atom) = match atom.it with
  | Domain.Atom.Keyword name -> name
  | Domain.Atom.Tag name -> "_" ^ name
  | other -> Domain.Atom.string_of_atom other

let rec substitute substitutions = function
  | Named (name, []) as typ -> Option.value (List.assoc_opt name substitutions) ~default:typ
  | Named (name, args) -> Named (name, List.map (substitute substitutions) args)
  | Sequence element -> Sequence (substitute substitutions element)
  | Optional element -> Optional (substitute substitutions element)
  | Tuple elements -> Tuple (List.map (substitute substitutions) elements)
  | typ -> typ

let instantiate definitions name arguments =
  let definition = match List.assoc_opt name definitions with
    | Some value -> value
    | None -> fail ("unknown, abstract external, or unbound observation type: " ^ name) in
  if List.length definition.parameters <> List.length arguments then
    fail ("type argument arity mismatch for " ^ name);
  let apply = substitute (List.combine definition.parameters arguments) in
  match definition.body with
  | Alias typ -> Alias (apply typ)
  | Record fields ->
      if definition.parameters <> [] then fail ("polymorphic record transport is unsupported: " ^ name);
      Record (List.map (fun (name, typ) -> name, apply typ) fields)
  | Variant arguments -> Variant (List.map apply arguments)
  | External -> External

let collect spec =
  let definitions = ref [] and relations = ref [] and extern_types = ref false in
  List.iter (fun (definition : S.def) -> match definition.it with
    | TypD (name, parameters, body, _) ->
        let body = match body.it with
          | PlainT typ -> Alias (convert typ)
          | StructT fields -> Record (List.map (fun (atom, typ) -> field_name atom, convert typ) fields)
          | VariantT cases -> Variant (List.concat_map (fun (notation, _, _) ->
              List.map convert (Domain.Mixfix.args notation.it)) cases) in
        definitions := !definitions @ [name.it, { parameters = List.map (fun (x : S.tparam) -> x.it) parameters; body }]
    | RelD (name, notation, inputs, _, _, _)
    | ExternRelD (name, notation, inputs, _) ->
        relations := !relations @ [{ name = name.it; inputs;
          arguments = List.map convert (Domain.Mixfix.args notation.it) }]
    | ExternTypD (name, _) ->
        extern_types := true;
        definitions := !definitions @ [name.it, { parameters = []; body = External }]
    | _ -> ()) spec;
  !definitions, !relations, !extern_types

let observations json =
  let root = fields "configuration" ["schema_version"; "observations"] json in
  if List.assoc "schema_version" root <> `Int 1 then fail "configuration: expected schema_version 1";
  let entries = match List.assoc "observations" root with
    | `List entries -> entries
    | _ -> fail "configuration: expected an observations array" in
  let seen = ref [] in
  List.map (fun entry ->
    let entry = fields "observation" ["id"; "relation"; "observe"] entry in
    let id = text "observation.id" (List.assoc "id" entry) in
    if List.mem id !seen then fail ("duplicate observation id: " ^ id);
    seen := id :: !seen;
    let relation_name = text "observation.relation" (List.assoc "relation" entry) in
    let selectors = match List.assoc "observe" entry with
      | `List values -> List.map (text "observation.observe") values
      | _ -> fail "observation.observe: expected an array" in
    { relation_name; selectors }) entries

let parse_selector value =
  let parts = String.split_on_char '.' value in
  match parts with
  | head :: fields when String.length head >= 2 && head.[0] = '%' && List.for_all ordinary fields ->
      let digits = String.sub head 1 (String.length head - 1) in
      if not (String.for_all digit digits) || (String.length digits > 1 && digits.[0] = '0') then
        fail ("invalid observation selector: " ^ value);
      let slot = match int_of_string_opt digits with Some slot when slot >= 0 -> slot
        | _ -> fail ("observation slot out of range: " ^ value) in
      slot, fields
  | _ -> fail ("invalid observation selector: " ^ value)

let rec prefix left right = match left, right with
  | [], _ -> true
  | x :: xs, y :: ys when x = y -> prefix xs ys
  | _ -> false

let rec selected_type definitions visited typ path = match path with
  | [] -> typ
  | field :: rest ->
      (match typ with
      | Named (name, args) ->
          if List.mem typ visited then fail ("alias cycle while selecting field " ^ field);
          (match instantiate definitions name args with
          | Alias underlying -> selected_type definitions (typ :: visited) underlying path
          | Record fields ->
              let field_type = match List.assoc_opt field fields with
                | Some value -> value
                | None -> fail ("unknown observation field " ^ name ^ "." ^ field) in
              selected_type definitions [] field_type rest
          | Variant _ | External -> fail ("field selector requires a record: " ^ name))
      | _ -> fail ("field selector requires a record: " ^ field))

let select definitions relations observations =
  let selected = ref [] and input_roots = ref [] and observation_roots = ref [] in
  List.iter (fun observation ->
    let relation = match List.find_opt (fun relation -> relation.name = observation.relation_name) relations with
      | Some relation -> relation
      | None -> fail ("unknown observation relation: " ^ observation.relation_name) in
    if not (List.exists (fun selected -> selected.name = relation.name) !selected) then (
      selected := !selected @ [relation];
      List.iteri (fun index typ -> if List.mem index relation.inputs then input_roots := typ :: !input_roots) relation.arguments);
    let previous = ref [] in
    List.iter (fun selector ->
      let slot, path = parse_selector selector in
      if slot >= List.length relation.arguments then fail ("observation slot out of range: " ^ selector);
      if List.mem slot relation.inputs then fail ("cannot observe an input slot: " ^ selector);
      if List.exists (fun (old_slot, old_path) -> old_slot = slot && (prefix path old_path || prefix old_path path)) !previous then
        fail ("duplicate or overlapping observation selectors: " ^ selector);
      previous := (slot, path) :: !previous;
      observation_roots := selected_type definitions [] (List.nth relation.arguments slot) path :: !observation_roots)
      observation.selectors) observations;
  !selected, List.rev !input_roots, List.rev !observation_roots

let rec key = function
  | Primitive name -> name
  | Named (name, []) -> name
  | Named (name, args) -> name ^ "<" ^ String.concat "," (List.map key args) ^ ">"
  | Sequence element -> "[" ^ key element ^ "]"
  | Optional element -> "?" ^ key element
  | Tuple elements -> "(" ^ String.concat "," (List.map key elements) ^ ")"
  | Function -> fail "function-valued observation transport is unsupported"

let rec lean_type = function
  | Primitive "bool" -> "_root_.Bool"
  | Primitive "nat" -> "_root_.Nat"
  | Primitive "int" -> "_root_.Int"
  | Primitive "text" -> "_root_.String"
  | Primitive name -> fail ("unsupported primitive " ^ name)
  | Named (name, args) ->
      let reference = "_root_.SpecTec." ^ quote name in
      if args = [] then reference else "(" ^ String.concat " " (reference :: List.map lean_type args) ^ ")"
  | Sequence element -> "(_root_.List " ^ lean_type element ^ ")"
  | Optional element -> "(_root_.Option " ^ lean_type element ^ ")"
  | Tuple elements -> "(" ^ String.concat " × " (List.map lean_type elements) ^ ")"
  | Function -> fail "function-valued observation transport is unsupported"

let children = function
  | Alias typ -> [typ]
  | Record fields -> List.map snd fields
  | Variant fields -> fields
  | External -> []

let metadata definitions namespace roots relations =
  let entries = ref [] and aliases = ref [] in
  let rec register ancestry typ =
    let name = key typ in
    if List.mem_assoc name !entries then name else (
      if List.length !entries >= 4096 then fail "observation type graph exceeds 4096 closed types";
      (match typ with
      | Named (name, args) when List.exists (function Named (previous, previous_args) ->
          name = previous && args <> previous_args | _ -> false) ancestry ->
          fail ("nonuniform recursive observation type is unsupported: " ^ name)
      | _ -> ());
      let alias = "Type" ^ string_of_int (List.length !entries) in
      let base = ["lean", string (namespace ^ "." ^ alias)] in
      entries := !entries @ [name, `Null];
      aliases := !aliases @ ["abbrev " ^ alias ^ " := " ^ lean_type typ];
      let register = register (typ :: ancestry) in
      let data = match typ with
        | Primitive _ -> ["kind", string "primitive"]
        | Sequence element | Optional element -> ignore (register element); ["kind", string "opaque"]
        | Tuple elements -> List.iter (fun typ -> ignore (register typ)) elements; ["kind", string "opaque"]
        | Named (raw, arguments) ->
            List.iter (fun typ -> ignore (register typ)) arguments;
            (match instantiate definitions raw arguments with
            | Alias underlying -> ["kind", string "alias"; "type", string (register underlying)]
            | Record fields ->
                let fields = List.map (fun (field, typ) ->
                  if not (ordinary field) then fail ("record field cannot be selected by observation schema: " ^ field);
                  field, object_ ["type", string (register typ); "lean", string field]) fields in
                ["kind", string "record"; "fields", object_ fields]
            | Variant arguments ->
                List.iter (fun typ -> ignore (register typ)) arguments;
                ["kind", string "variant"]
            | External -> ["kind", string "opaque"])
        | Function -> fail "function-valued observation transport is unsupported" in
      entries := List.map (fun (key, value) -> key, if key = name then object_ (base @ data) else value) !entries;
      name) in
  List.iter (fun typ -> ignore (register [] typ)) roots;
  let relations = List.mapi (fun index relation ->
    let arguments = List.map (fun typ -> object_ ["type", string (register [] typ)]) relation.arguments in
    let alias = "Relation" ^ string_of_int index in
    aliases := !aliases @ ["noncomputable abbrev " ^ alias ^ " := _root_.SpecTec." ^ quote relation.name];
    relation.name, object_ ["lean", string (namespace ^ "." ^ alias);
      "inputs", array (List.map (fun index -> `Int index) relation.inputs); "arguments", array arguments]) relations in
  object_ ["schema_version", `Int 1; "namespace", string namespace;
    "types", object_ !entries; "relations", object_ relations], !aliases

let codec_declarations definitions codec roots =
  let visited = ref [] and active = ref [] and derived = ref [] in
  let rec visit typ =
    if List.mem typ !visited then () else (
      if List.length !visited >= 4096 then fail "codec dependency graph exceeds 4096 closed types";
      visited := typ :: !visited;
      match typ with
      | Primitive _ -> ()
      | Sequence element | Optional element -> visit element
      | Tuple elements -> List.iter visit elements
      | Function -> fail "function-valued JSON transport is unsupported"
      | Named (name, arguments) ->
          if List.exists (fun (previous, args) -> name = previous && args <> arguments) !active then
            fail ("nonuniform recursive codec is unsupported: " ^ name);
          active := (name, arguments) :: !active;
          List.iter visit arguments;
          let body = instantiate definitions name arguments in
          List.iter visit (children body);
          active := List.tl !active;
          (match body with
          | Alias _ -> ()
          | External | Record _ | Variant _ ->
              (* Ordered translation emits each external type as a singleton
                 inductive, so its codecs and dependent record codecs derive. *)
              if not (List.mem name !derived) then
                derived := !derived @ [name])) in
  List.iter visit roots;
  let declarations = List.map (fun name -> "deriving instance _root_.Lean." ^ codec ^ " for _root_.SpecTec." ^ quote name) !derived in
  let checks = List.mapi (fun index typ ->
    "private abbrev required" ^ codec ^ string_of_int index ^ " : _root_.Lean." ^ codec ^
      " (" ^ lean_type typ ^ ") := inferInstance") (List.sort_uniq compare roots) in
  declarations @ checks

let generate spec_module namespace transport_model property_inputs configuration spec =
  let spec_module = qualified "spec module" spec_module in
  let lean_namespace = qualified "transport namespace" namespace in
  let observations = observations configuration in
  let definitions, relations, _external_types = collect spec in
  let relations, inputs, observed = select definitions relations observations in
  let inputs = property_inputs @ inputs in
  let manifest, aliases = metadata definitions namespace property_inputs relations in
  let codecs = codec_declarations definitions "ToJson" inputs @
    codec_declarations definitions "FromJson" (inputs @ observed) in
  let transport = String.concat "\n" (["import Lean"; "import " ^ spec_module;
    ""; "set_option autoImplicit false"; "set_option linter.unusedVariables false";
    ""; "namespace " ^ lean_namespace; ""; Option.value transport_model ~default:""; ""] @ codecs @ [""] @ aliases @
    [""; "end " ^ lean_namespace; ""]) in
  object_ ["manifest", manifest; "transport", string transport]

let property_inputs paths path name =
  if path = "" && name = "" then [] else (
    if path = "" || name = "" then fail "--property and --property-name are required together";
    let source, properties, _ = Property_document.load paths path in
    let property = match List.filter (fun ((id:Lang.El.id),_,_,_) -> id.it = name) properties with
      | [property] -> property
      | _ -> fail ("expected one property named " ^ name) in
    match Pass.elab_property source property with
    | Ok (_,inputs,_,_) -> List.map (fun (_,typ) -> convert typ) inputs
    | Error diagnostic -> fail (Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain (Diagnostic.Report.singleton diagnostic)))

let main () =
  let spec_module = ref "" and namespace = ref "" and config = ref "" and paths = ref [] and model = ref None in
  let property = ref "" and property_name = ref "" in
  Arg.parse ["--property", Arg.Set_string property, "Property clause whose explicit inputs require codecs";
    "--property-name", Arg.Set_string property_name, "Name of the property clause";
    "--spec-module", Arg.Set_string spec_module, "Raw donor Lean module";
    "--namespace", Arg.Set_string namespace, "Transport alias namespace";
    "--config", Arg.Set_string config, "Observation configuration JSON";
    "--transport-model", Arg.String (fun path -> model := Some path), "Lean model declarations inserted inside the transport namespace"]
    (fun path -> paths := !paths @ [path]) "metadata --spec-module MODULE --namespace NAME --config CONFIG_JSON SPEC...";
  if !spec_module = "" || !namespace = "" || !config = "" || !paths = [] then fail "required metadata arguments are missing";
  let configuration = Yojson.Basic.from_file !config in
  let spec = if !property = "" then match Pass.elab !paths with
    | Ok spec -> spec
    | Error diagnostic -> fail (Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain (Diagnostic.Report.singleton diagnostic))
    else let source, _, _ = Property_document.load !paths !property in
      match Pass.elab_spec source with
      | Ok spec -> spec
      | Error diagnostic -> fail (Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain (Diagnostic.Report.singleton diagnostic)) in
  let transport_model = Option.map (fun path ->
    let channel = open_in_bin path in
    Fun.protect ~finally:(fun () -> close_in channel)
      (fun () -> really_input_string channel (in_channel_length channel))) !model in
  let inputs = property_inputs !paths !property !property_name in
  let result = generate !spec_module !namespace transport_model inputs configuration spec in
  print_endline (Yojson.Basic.to_string result)

let () =
  try main () with
  | Frontend.Error.ParseError diagnostic ->
      prerr_endline (Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain (Diagnostic.Report.singleton diagnostic)); exit 1
  | Invalid_metadata message | Sys_error message | Yojson.Json_error message ->
      prerr_endline ("observation metadata: " ^ message); exit 1
