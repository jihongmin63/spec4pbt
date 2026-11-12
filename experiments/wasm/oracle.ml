(** Execute the pinned specification's Module_ok through its native AL interpreter.
    JSON follows the repository's Lean-derived constructor representation. *)
open Util.Source
open Lang.Il
module Mixfix = Domain.Mixfix
module Value = Runtime.Value
module Run = Runtime.Dynamic_Runner.Signature

let fail message = raise (Failure message)
let report diagnostic = Diagnostic.Render.render_report ~ansi:Diagnostic.Ansi.plain
  (Diagnostic.Report.singleton diagnostic)
let unwrap = function Ok value -> value | Error diagnostic -> fail (report diagnostic)

module NoExternal = struct
  module Cache = struct let cache_on () = () let cache_off () = () end
  let blocked name = Run.Fail (Run.abort ~source:"wasm-oracle" no_region
    ("unexpected external call: " ^ name))
  let eval_extern_rel name _ = blocked name
  let eval_extern_func name _ _ = blocked name
  let checkpoint () = 0
  let seff _ _ = false
  let clear () = ()
  let init_mode _ = Ok ()
end
module Eval = Interp_al.Interp.Make (Interface.SpecTec_AL) (NoExternal) ()

(* Match translator/src/translator.ml's canonical constructor naming. *)
let prefix_name notation =
  let atom = match notation with
    | Mixfix.Atom atom -> Some atom
    | Mixfix.Seq (Mixfix.Atom atom :: rest)
      when List.for_all (function Mixfix.Arg _ -> true | _ -> false) rest -> Some atom
    | _ -> None in
  match atom with
  | Some {it = Domain.Atom.Keyword name; _} -> Some name
  | Some {it = Domain.Atom.Tag name; _} -> Some ("_" ^ name)
  | _ -> None

let rec parts = function
  | Mixfix.Arg _ -> ["%"]
  | Mixfix.Atom atom -> [Domain.Atom.string_of_atom atom.it]
  | Mixfix.Brack (left, inner, right) ->
      parts (Mixfix.Atom left) @ parts inner @ parts (Mixfix.Atom right)
  | Mixfix.Infix (left, atom, right) -> parts left @ parts (Mixfix.Atom atom) @ parts right
  | Mixfix.Seq items -> List.concat_map parts items

let named_cases cases =
  let prefixes = List.filter_map (fun (notation, _, _) -> prefix_name notation.it) cases in
  List.map (fun (notation, _, _) ->
    let name = match prefix_name notation.it with
      | Some name when List.length (List.filter (String.equal name) prefixes) = 1 -> name
      | _ -> String.concat " " (parts notation.it) in
    name, notation) cases

let object_fields = function `Assoc fields -> fields | _ -> fail "expected JSON object"
let integer = function
  | `Int value -> Bigint.of_int value
  | `Intlit value -> Bigint.of_string value
  | _ -> fail "expected JSON integer"

let rec unique_json = function
  | `Assoc fields ->
      let names = List.map fst fields in
      if List.length names <> List.length (List.sort_uniq String.compare names)
      then fail "duplicate JSON object field";
      List.iter (fun (_, value) -> unique_json value) fields
  | `List values -> List.iter unique_json values
  | _ -> ()

let rec decode definitions (typ : typ) json : Value.t =
  match typ.it, json with
  | BoolT, `Bool value -> Value.Make.bool value
  | NumT `NatT, (`Int _ | `Intlit _) ->
      let value = integer json in
      if Bigint.compare value Bigint.zero < 0 then fail "negative natural number";
      Value.Make.nat value
  | NumT `IntT, (`Int _ | `Intlit _) -> Value.Make.int (integer json)
  | TextT, `String value -> Value.Make.text value
  | TupleT types, `List values when List.length types = List.length values ->
      Value.Make.tuple typ (List.map2 (decode definitions) types values)
  | IterT (inner, List), `List values ->
      Value.Make.list typ (List.map (decode definitions inner) values)
  | IterT (_, Opt), `Null -> Value.Make.opt typ None
  | IterT (inner, Opt), value -> Value.Make.opt typ (Some (decode definitions inner value))
  | VarT (id, arguments), _ ->
      let parameters, definition = match List.assoc_opt id.it definitions with
        | Some definition -> definition
        | None -> fail ("undefined specification type: " ^ id.it) in
      if List.length parameters <> List.length arguments then fail ("type arity: " ^ id.it);
      let substitution = Domain.Lib.TIdMap.of_lists parameters arguments in
      let substitute = Type.Subst.subst_typ substitution in
      (match definition.it with
      | PlainT alias -> decode definitions (substitute alias) json
      | StructT fields ->
          let actual = object_fields json in
          let name atom = Domain.Atom.string_of_atom atom.it in
          let expected = List.map (fun (atom, _) -> name atom) fields in
          if List.sort String.compare expected <> List.sort String.compare (List.map fst actual)
          then fail ("record fields mismatch for " ^ id.it);
          Value.Make.str typ (List.map (fun (atom, inner) ->
            atom, decode definitions (substitute inner) (List.assoc (name atom) actual)) fields)
      | VariantT cases ->
          let name, payload = match json with
            | `String name -> name, None
            | `Assoc [name, payload] -> name, Some payload
            | _ -> fail ("expected constructor of " ^ id.it) in
          let notation = match List.assoc_opt name (named_cases cases) with
            | Some notation -> Type.Subst.subst_nottyp substitution notation
            | None -> fail ("unknown constructor " ^ id.it ^ "." ^ name) in
          let types = Mixfix.args notation.it in
          let values = match types, payload with
            | [], None -> []
            | [_], Some value -> [value]
            | _, Some (`List values) when List.length values = List.length types -> values
            | _ -> fail ("constructor argument count mismatch: " ^ id.it ^ "." ^ name) in
          Value.Make.case typ (Mixfix.fill (Mixfix.to_mixop notation.it)
            (List.map2 (decode definitions) types values)))
  | _ -> fail ("JSON does not match " ^ Lang.Il.Print.string_of_typ typ)

let main () =
  if Array.length Sys.argv <> 2 then fail "Usage: oracle.exe WASM_SPEC_DIRECTORY < modules.jsonl";
  Wasm_builtin_hooks.Builtin_hooks.init ();
  let spec = unwrap (Pass.elab [Sys.argv.(1)]) in
  let algorithm = unwrap (Pass.algo_spec spec) in
  unwrap (Eval.init ~cache:false ~det:false ~guard:true algorithm);
  let definitions = List.filter_map (fun (definition : def) -> match definition.it with
    | TypD (id, parameters, body, _) -> Some (id.it, (parameters, body))
    | _ -> None) spec in
  let module_type = VarT ("module" $ no_region, []) $ no_region in
  let rec consume index = match input_line stdin with
    | line ->
        let json = Yojson.Safe.from_string line in
        unique_json json;
        let value = decode definitions module_type json in
        let result = match Eval.eval_rel "Module_ok" [value] with
          | Run.Pass _ -> `Assoc ["index", `Int index; "module_ok", `Bool true]
          | Run.Fail (Run.Unmatch traces) ->
              `Assoc ["index", `Int index; "module_ok", `Bool false;
                "diagnostic", `String (report (Run.diagnostic_of_failure (Run.Unmatch traces)))]
          | Run.Fail (Run.Abort diagnostic) -> fail (report diagnostic) in
        print_endline (Yojson.Safe.to_string result);
        consume (index + 1)
    | exception End_of_file -> () in
  consume 0

let () = main ()
