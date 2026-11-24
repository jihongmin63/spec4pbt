open Util.Source
open Lang
open Lang.Il
open Lang.Al

module Run = Runtime.Dynamic_Runner.Signature
module Value = Runtime.Value

module Interface_ = struct
  include Interface.SpecTec_AL
  let call_builtin add id targs values =
    if id.it = Instrumentation.marker_name then
      (match values with
       | [phase; relation; kind; source; inputs; outputs; input_slots] ->
           Instrumentation.record_marker (Value.Get.text phase)
             (Value.Get.text relation) (Value.Get.text kind)
             (Value.Get.text source) (Value.Get.text inputs)
             (Value.Get.text outputs) (Value.Get.text input_slots);
           Value.Make.bool true
       | _ -> failwith "invalid trace marker arguments")
    else if String.starts_with ~prefix:Instrumentation.identity_prefix id.it then
      (match values with
       | [_; value; _] -> value
       | _ -> failwith "invalid trace identity arguments")
    else if String.starts_with ~prefix:"property_observe_" id.it then
      (match values with
       | [name; value] ->
           Instrumentation.record (Value.Get.text name)
             (string_of_region id.at) value;
           Value.Make.bool true
       | _ -> failwith "invalid observation builtin arguments")
    else Interface.SpecTec_AL.call_builtin add id targs values
end

let field json key = Yojson.Safe.Util.member key json
let string_field json key = Yojson.Safe.Util.to_string (field json key)
let list_field json key = Yojson.Safe.Util.to_list (field json key)
let emit json = print_endline (Yojson.Safe.to_string json)

let rec value_of_json json =
  let typ = string_field json "type" in
  let raw = field json "value" in
  match typ, raw with
  | "nat", `Int n when n >= 0 -> Value.Make.nat (Bigint.of_int n)
  | "nat", `String n -> Value.Make.nat (Bigint.of_string n)
  | "int", `Int n -> Value.Make.int (Bigint.of_int n)
  | "int", `String n -> Value.Make.int (Bigint.of_string n)
  | "text", `String s -> Value.Make.text s
  | "bool", `Bool b -> Value.Make.bool b
  | name, `Null when field json "constructor" <> `Null ->
      let constructor = string_field json "constructor" in
      let args = List.map value_of_json (list_field json "args") in
      let mixop = match Type_metadata.mixop_of_constructor name constructor with
        | Some mixop -> mixop
        | None ->
            (* The standalone codec probe also accepts undeclared prefix types. *)
            let pattern = constructor ^ String.concat "" (List.map (fun _ -> " _") args) in
            Value.Mixops.of_string pattern in
      let typ = Runtime.Type.Typ.Make.var (name $ no_region) [] in
      Value.Make.case typ (Domain.Mixfix.fill mixop args)
  | _ -> failwith ("invalid typed value: " ^ Yojson.Safe.to_string json)

let rec json_of_value value =
  match value.it with
  | BoolV b -> `Assoc ["type", `String "bool"; "value", `Bool b]
  | NumV (`Nat n) -> `Assoc ["type", `String "nat"; "value", `String (Bigint.to_string n)]
  | NumV (`Int n) -> `Assoc ["type", `String "int"; "value", `String (Bigint.to_string n)]
  | TextV s -> `Assoc ["type", `String "text"; "value", `String s]
  | CaseV valuecase ->
      let mixop, args = Domain.Mixfix.split valuecase in
      let typ = Type_metadata.wire_type (value.note.typ $ value.at) in
      let constructor = Type_metadata.constructor_of_mixop typ mixop in
      `Assoc ["type", `String typ;
              "constructor", `String constructor;
              "args", `List (List.map json_of_value args)]
  | _ -> failwith ("unsupported value: " ^ Value.to_string value)

let active_external : (string * int list) list ref = ref []
let external_events : Yojson.Safe.t list ref = ref []

module MakeExtern (IA : Run.INTERP_AL) (IS : Run.INTERP_SL) (IP : Run.INTERP_PL) = struct
  module Base = Backend_boot.Spectec.Make_null (Interface_) (IA) (IS) (IP)
  include Base

  let eval_extern_rel name values =
    match List.assoc_opt name !active_external with
    | None -> Base.eval_extern_rel name values
    | Some positions ->
        let current = !(Interface_.Builtin_SpecTec.ctr) in
        let input_json = `List (List.map json_of_value values) in
        emit (`Assoc ["kind", `String "external_call";
                      "relation", `String name;
                      "input", input_json;
                      "fresh_id", `Int current;
                      "observed_outputs", `List (List.map (fun x -> `Int x) positions)]);
        let response = Yojson.Safe.from_string (read_line ()) in
        let next = Yojson.Safe.Util.to_int (field response "fresh_id") in
        if next < 0 then failwith "fresh_id must be a natural number";
        let status = string_field response "status" in
        if status = "no_match" then begin
          Interface_.Builtin_SpecTec.ctr := next;
          external_events := `Assoc ["seq", `Int (Instrumentation.tick ());
            "relation", `String name;
            "input", input_json; "status", `String status;
            "fresh_before", `Int current; "fresh_after", `Int next]
            :: !external_events;
          Run.Fail (Run.Unmatch [])
        end else if status = "returned" then begin
          let outputs = list_field response "outputs" in
          let actual = List.map (fun item ->
            Yojson.Safe.Util.to_int (field item "position"),
            value_of_json (field item "value")) outputs in
          let found = List.map fst actual in
          if found <> positions then
            failwith "adapter outputs do not match observed output positions";
          Interface_.Builtin_SpecTec.ctr := next;
          external_events := `Assoc ["seq", `Int (Instrumentation.tick ());
            "relation", `String name;
            "input", input_json; "status", `String status;
            "outputs", `List (List.map (fun (position, value) ->
              `Assoc ["position", `Int position; "value", json_of_value value]) actual);
            "fresh_before", `Int current; "fresh_after", `Int next]
            :: !external_events;
          Run.Pass (List.map snd actual)
        end else failwith ("invalid adapter status: " ^ status)
end

module Runner_ = Runner.Make.Make_rec (Interface_) (MakeExtern)
    (Interp_al.Interp.Make) (Interp_sl.Interp.Make) (Interp_pl.Interp.Make)

let relation_name = function
  | { it = RelD (id, _, _, _, _, _); _ }
  | { it = ExternRelD (id, _, _, _); _ } -> Some id.it
  | _ -> None

let unsupported_constructs def =
  let module C = Lang.Al.Walk.Collect in
  let item kind at = `Assoc ["kind", `String kind;
                             "source", `String (string_of_region at)] in
  let collector = { (C.make_base ~default:[] ~compose:( @ )) with
    collect_exp = (fun collector exp ->
      let nested = C.default_collect_exp collector exp in
      match exp.it with
      | IterE _ -> item "iteration" exp.at :: nested
      | _ -> nested);
    collect_arg = (fun collector arg ->
      match arg.it with
      | DefA _ -> [item "higher_order" arg.at]
      | _ -> C.default_collect_arg collector arg);
    collect_prem = (fun collector prem ->
      let nested = C.default_collect_prem collector prem in
      match prem.it with
      | IfNotHoldPr _ -> item "negation" prem.at :: nested
      | IterPr _ -> item "iteration" prem.at :: nested
      | _ -> nested) } in
  let path path =
    let _, prems, outputs = path in
    C.collect_prems collector prems @ C.collect_exps collector outputs in
  let group group =
    let _, (_, inputs, match_prems), paths = group.it in
    C.collect_exps collector inputs @ C.collect_prems collector match_prems @
    List.concat_map path paths in
  match def.it with
  | RelD (_, _, _, groups, elsegroup, _) ->
      let fallback = match elsegroup with
        | None -> []
        | Some elsegroup ->
            let _, (_, inputs, match_prems), fallback_path = elsegroup.it in
            item "otherwise" elsegroup.at ::
            (C.collect_exps collector inputs @ C.collect_prems collector match_prems @
             path fallback_path) in
      List.concat_map group groups @ fallback
  | _ -> []

let relation_metadata def =
  let details id nottyp inputs rule_count rule_inputs defined =
    let typs = Domain.Mixfix.args nottyp.it in
    let input_typs, output_typs = Hints.Input.split inputs typs in
    let typ_json typ = `String (Type_metadata.wire_type typ) in
    let name_json exp = match exp.it with
      | VarE id -> `String id.it
      | _ -> `Null in
    `Assoc ["name", `String id.it;
            "defined", `Bool defined;
            "source", `String (string_of_region id.at);
            "input_types", `List (List.map typ_json input_typs);
            "output_types", `List (List.map typ_json output_typs);
            "rule_count", `Int rule_count;
            "rule_inputs", `List (List.map name_json rule_inputs);
            "unsupported_constructs", `List (unsupported_constructs def)]
  in
  match def.it with
  | ExternRelD (id, nottyp, inputs, _) ->
      Some (details id nottyp inputs 0 [] false)
  | RelD (id, nottyp, inputs, groups, elsegroup, _) ->
      let paths = List.concat_map (fun group ->
        let _, _, paths = group.it in paths) groups in
      let rule_count = List.length paths + (if Option.is_some elsegroup then 1 else 0) in
      let rule_inputs = match groups with
        | group :: _ -> let _, (_, inputs, _), _ = group.it in inputs
        | [] -> [] in
      Some (details id nottyp inputs rule_count rule_inputs true)
  | _ -> None

let check spec =
  let relations = List.filter_map relation_name spec in
  let definitions = List.filter_map relation_metadata spec in
  let graph = External_analysis.relations spec in
  let definitions = List.map(fun json ->
    let name = string_field json "name" in
    let missing = External_analysis.reachable graph name |> List.filter(fun name ->
      not (External_analysis.find graph name).External_analysis.defined) in
    `Assoc(("missing_dependencies",`List(List.map(fun x->`String x)missing)) ::
      Yojson.Safe.Util.to_assoc json))definitions in
  emit (`Assoc ["relations", `List (List.map (fun x -> `String x) relations);
                "definitions", `List definitions;
                "type_schema", Type_metadata.schema spec])

let codec () =
  let input = Yojson.Safe.from_string (read_line ()) |> Yojson.Safe.Util.to_list in
  emit (`List (List.map (fun item -> json_of_value (value_of_json item)) input))

let result_values = function
  | Run.Pass values -> Some values
  | Run.Fail (Run.Unmatch _) -> None
  | Run.Fail (Run.Abort _) -> None

let al_md5 spec =
  Digest.to_hex (Digest.string
    (Lang.Al.Print.string_of_spec (Instrumentation.instrument spec)))

let execute spec request =
  Instrumentation.reset ();
  external_events := [];
  let spec = match field request "instrument" with
    | `Bool false -> spec
    | _ -> Instrumentation.instrument spec in
  let al_hash = Digest.to_hex (Digest.string (Lang.Al.Print.string_of_spec spec)) in
  let pre = string_field request "pre" in
  let goal = string_field request "goal" in
  let input = List.map value_of_json (list_field request "input") in
  (match Runner_.init ~cache:false ~det:false ~guard:true (Run.AL spec) with
  | Ok () -> ()
  | Error _ -> failwith "native runner initialization failed");
  Interface_.Builtin_SpecTec.ctr := 0;
  let pre_result = result_values (Runner_.Interp.eval_rel pre input) in
  let status, pre_outputs, goal_outputs =
    match pre_result with
    | None -> "precondition_failed", [], []
    | Some values ->
        let goal_result = result_values (Runner_.Interp.eval_rel goal (input @ values)) in
        (if Option.is_some goal_result then "passed" else "failed"),
        values, Option.value ~default:[] goal_result
  in
  emit (`Assoc ["status", `String status;
                "al_md5", `String al_hash;
                "pre_outputs", `List (List.map json_of_value pre_outputs);
                "goal_outputs", `List (List.map json_of_value goal_outputs);
                "bindings", `List (List.map (fun (event : Instrumentation.observation) ->
                  `Assoc ["seq", `Int event.Instrumentation.seq;
                          "label", `String event.Instrumentation.label;
                          "source", `String event.source;
                          "value", json_of_value event.value])
                  (Instrumentation.snapshot ()));
                "markers", `List (List.map (fun (event : Instrumentation.marker) ->
                  `Assoc ["seq", `Int event.Instrumentation.seq;
                          "phase", `String event.phase;
                          "relation", `String event.relation;
                          "kind", `String event.kind;
                          "source", `String event.source;
                          "inputs", `List (List.map (fun x -> `String x) event.inputs);
                          "input_slots", `List (List.map (fun slot ->
                            `List (List.map (fun x -> `String x) slot)) event.input_slots);
                          "outputs", `List (List.map (fun x -> `String x) event.outputs)])
                  (Instrumentation.marker_snapshot ()));
                "external_calls", `List (List.rev !external_events);
                "fresh_id", `Int !(Interface_.Builtin_SpecTec.ctr)])

let debug spec =
  active_external := [];
  execute spec (Yojson.Safe.from_string (read_line ()))

let replay spec =
  let request = Yojson.Safe.from_string (read_line ()) in
  let external_entries = list_field request "external" in
  let map = List.map (fun item ->
    let name = string_field item "relation" in
    let positions = List.map Yojson.Safe.Util.to_int
      (list_field item "observed_outputs") in
    if List.length positions <> List.length (List.sort_uniq compare positions)
    then failwith "duplicate observed output slot";
    name, positions) external_entries in
  active_external := map;
  let projection = match field request "projection" with
    | `Null -> map
    | `Assoc pairs -> List.map (fun (name, positions) ->
        name, List.map Yojson.Safe.Util.to_int
          (Yojson.Safe.Util.to_list positions)) pairs
    | _ -> failwith "projection must be an object" in
  let lowered = Replay_lowering.lower spec projection (List.map fst map) in
  execute lowered request

let analyze spec =
  let request = Yojson.Safe.from_string (read_line ()) in
  let pre = string_field request "pre" in
  let goal = string_field request "goal" in
  let map = List.map (fun item ->
    string_field item "relation",
    List.map Yojson.Safe.Util.to_int (list_field item "observed_outputs"))
      (list_field request "external") in
  let report = Observability.analyze spec pre goal map in
  let projection = field report "projection" |> Yojson.Safe.Util.to_assoc
    |> List.map (fun (name, positions) ->
        name, List.map Yojson.Safe.Util.to_int
          (Yojson.Safe.Util.to_list positions)) in
  let lowered = Replay_lowering.lower spec projection (List.map fst map) in
  let fields = Yojson.Safe.Util.to_assoc report in
  emit (`Assoc (("al_md5", `String (al_md5 lowered)) :: fields))

let debug_check spec =
  let request = Yojson.Safe.from_string (read_line ()) in
  let relations = External_analysis.relations spec in
  let needed = List.sort_uniq String.compare
    (External_analysis.reachable relations (string_field request "pre") @
     External_analysis.reachable relations (string_field request "goal")) in
  let missing = List.filter (fun name ->
    not (External_analysis.find relations name).External_analysis.defined)
      needed in
  emit (`Assoc ["al_md5", `String (al_md5 spec);
                "available", `Bool (missing = []);
                "missing", `List (List.map (fun x -> `String x) missing)])

let () =
  try
    if Array.length Sys.argv < 3 then failwith "usage: main check|debug spec.watsup";
    let mode = Sys.argv.(1) in
    let path = Sys.argv.(2) in
    match P4spectec.algo [path] with
    | Error error ->
        let report = P4spectec.Error.to_report error in
        prerr_endline (Diagnostic.Render.render_report
          ~ansi:Diagnostic.Ansi.plain report);
        exit 2
    | Ok spec ->
        Type_metadata.active := spec;
        (match mode with
        | "check" -> check spec
        | "codec" -> codec ()
        | "analyze" ->
            (try analyze spec with Failure message as error ->
              (match Observability.failure_evidence () with
               | None -> ()
               | Some evidence ->
                   let fields = Yojson.Safe.Util.to_assoc evidence in
                   emit (`Assoc ["status", `String "compile_error";
                                 "error", `String message;
                                 "analysis", `Assoc (
                                   ("spec_al_md5", `String (al_md5 spec)) :: fields)]));
              raise error)
        | "debug-check" -> debug_check spec
        | "dump" -> print_string (Lang.Al.Print.string_of_spec spec)
        | "debug" -> debug spec
        | "replay" -> replay spec
        | _ -> failwith ("unsupported mode: " ^ mode))
  with exn ->
    prerr_endline (Printexc.to_string exn);
    exit 2
