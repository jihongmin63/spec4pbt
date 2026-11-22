open Util.Source

exception Input_error of region * string

let profile_name = ref ""
let inputs = ref []
let output = ref ""
let manifest_path = ref ""
let inventory = ref false
let data_only = ref false
let options = [
  "--profile", Arg.Set_string profile_name, "NAME profile namespace";
  "--input", Arg.String (fun p -> inputs := p :: !inputs), "PATH ordered source input (repeatable)";
  "--output", Arg.Set_string output, "DIR output directory";
  "--manifest", Arg.Set_string manifest_path, "FILE execution manifest";
  "--inventory", Arg.Set inventory, " collect AL inventory only";
  "--data-only", Arg.Set data_only, " generate all AL datatypes and structural support"
]

let rec mkdir path =
  if path <> "" && not (Sys.file_exists path) then (
    mkdir (Filename.dirname path); Unix.mkdir path 0o755)

let write_json path json =
  mkdir (Filename.dirname path);
  let channel = open_out path in
  Fun.protect ~finally:(fun () -> close_out channel)
    (fun () -> Yojson.Safe.pretty_to_channel channel json; output_char channel '\n')

let file_sha256 path =
  let channel = Unix.open_process_args_in "sha256sum" [|"sha256sum"; "--"; path|] in
  let line = input_line channel in
  match Unix.close_process_in channel with
  | Unix.WEXITED 0 -> String.sub line 0 64
  | _ -> failwith ("sha256sum failed: " ^ path)

let frontend_diagnostic (d : Diagnostic.t) =
  { Coq_ir.stage = d.source; location = d.region; construct = "frontend";
    reason = d.message ^ (match d.detail with None -> "" | Some detail -> "\n" ^ detail) }

let report d =
  Printf.eprintf "%s: %s [%s]: %s\n%!"
    (string_of_region d.Coq_ir.location) d.stage d.construct d.reason

let assoc_update updates = function
  | `Assoc fields -> `Assoc (updates @ List.filter(fun(k,_)->not(List.mem_assoc k updates))fields)
  | _ -> invalid_arg "expected JSON object"

let audit_generation (context:Context.t) data (bodies:Coq_ir.body list) =
  let exact label expected actual =
    let unique=List.sort_uniq String.compare actual in
    if List.length unique<>List.length actual then
      raise(Input_error(no_region,"duplicate generated " ^ label));
    if List.sort String.compare expected<>unique then
      raise(Input_error(no_region,"generated " ^ label ^ " do not exactly cover the AL inventory")) in
  let type_names=List.concat_map(fun(m:Coq_ir.data_module)->List.map Data.declaration_name m.declarations)data in
  let callable=List.filter(fun(d:Context.declaration)->Option.is_some d.signature)context.declarations in
  let types=List.filter(fun(d:Context.declaration)->d.namespace="type")context.declarations in
  exact "types" (List.map(fun(d:Context.declaration)->d.generated_name)types)type_names;
  exact "bodies" (List.map(fun(d:Context.declaration)->d.generated_name)callable)
    (List.map(fun(b:Coq_ir.body)->b.call_name)bodies);
  let bindings=match Builtins.bindings context with `List xs->xs|_->assert false in
  let get key = function `Assoc fields->(match List.assoc_opt key fields with Some(`String x)->x|_->raise(Input_error(no_region,"builtin binding missing " ^ key)))|_->raise(Input_error(no_region,"invalid builtin binding")) in
  let builtin_names=List.filter_map(fun(d:Context.declaration)->if d.kind="BuiltinDecD" then Some d.source_name else None)context.declarations in
  exact "builtin bindings" builtin_names (List.map(get "source_name")bindings);
  (* Small real-Coq fixtures can select a profile while supplying fewer source
     declarations. The driver checks the pinned whole-profile count (47/76);
     this frontend audits exact coverage of its actual complete input AL. *)
  let bindings=List.map(fun binding->
    let name=get "source_name" binding in
    let d=Option.get(Context.find context ~namespace:"dec" name) in
    let implementation,source=if context.profile.name<>"wasm" || List.mem name ["union_set";"diff_set"] then
      get "runtime_helper" binding,"translator/coq/Builtins/P4.v" else
      if name="lsl_" || List.mem name Wasm_bindings.plain || List.mem name Wasm_bindings.partial then
        "WasmScalar."^name,"translator/coq/Builtins/WasmScalar.v" else
      if String.starts_with ~prefix:"f32_" name || String.starts_with ~prefix:"f64_" name then
        "WasmFloat." ^ (if String.ends_with ~suffix:"of_bytes" name then "of_bytes" else
          if List.exists(fun x->String.ends_with ~suffix:x name)["_eq";"_ne";"_le"] then "compare" else "binary"),"translator/coq/Builtins/WasmFloat.v" else
      if String.starts_with ~prefix:"eval_v" name then "WasmVector."^name,"translator/coq/Builtins/WasmVector.v"
      else "WasmExecution."^name,"translator/coq/Builtins/WasmExecution.v" in
    let old=match binding with `Assoc fs->fs|_->assert false in
    assoc_update (["profile",`String context.profile.name;"declaration_kind",`String d.kind;
      "generated_name",`String d.generated_name;"runtime_helper",`String implementation;
      "runtime_source",`String source] @
      if List.mem_assoc "native_source" old then [] else
        ["native_source",`String(if name="lsl_" then "p4spec/lib/interface/builtin/numerics.ml" else "p4spec/lib/interface/builtin/nats.ml")]) binding)bindings in
  let completed=List.map(fun(d:Context.declaration)->{d with disposition=
    if d.namespace="var" then "consumed-metadata" else if d.namespace="type" then "generated-type"
    else if Option.is_some d.signature then "generated-body"
    else raise(Input_error(d.location,"unclassified AL declaration"))})context.declarations in
  let counts=["generated-type",List.length types;"generated-body",List.length bodies;
    "consumed-metadata",List.length context.variable_metadata;"pending",0;"skipped",0] in
  completed,bindings,`Assoc(List.map(fun(k,v)->k,`Int v)counts)

let output_hashes root =
  let rec walk relative =
    let dir=if relative="" then root else Filename.concat root relative in
    Sys.readdir dir |> Array.to_list |> List.sort String.compare |> List.concat_map(fun name->
      let rel=if relative="" then name else Filename.concat relative name in
      let path=Filename.concat root rel in
      if Sys.is_directory path then walk rel else if Filename.check_suffix name ".v" then
        [`Assoc["path",`String rel;"sha256",`String(file_sha256 path)]] else []) in
  walk ""

let run () =
  Arg.parse options (fun value -> raise (Arg.Bad ("unexpected positional argument: " ^ value)))
    "al-to-coq --profile NAME --input PATH ... --output DIR --manifest FILE [--inventory]";
  inputs := List.rev !inputs;
  if !profile_name = "" || !inputs = [] || !output = "" || !manifest_path = "" then (
    Arg.usage options "all of --profile, --input, --output and --manifest are required"; exit 2);
  let files = ref [] in
  let status = ref "failed" in
  let diagnostics = ref [] in
  let warnings = ref [] in
  let definition_count = ref `Null in
  let source_count = ref `Null in
  let raw_definition_count = ref `Null in
  let normalizations = ref [] in
  let generation_complete=ref false and output_files=ref [] and builtin_bindings=ref [] in
  let disposition_counts=ref `Null in
  let result =
    try
      files := List.map (fun path ->
        if not (Sys.file_exists path) || Sys.is_directory path then
          raise (Input_error (region_of_file path, "input must be an existing source file"));
        `Assoc ["path", `String path; "sha256", `String (file_sha256 path)]) !inputs;
      (* Use the pinned public frontend directly, with no patched algo_defs and
         no reconstruction of IL from algorithmic rule groups. *)
      let (parsed, parse_warnings) = Diagnostic.collect (fun () -> Pass.parse !inputs) in
      warnings := List.map frontend_diagnostic (Diagnostic.Report.to_sorted_list parse_warnings);
      match parsed with
      | Error d -> diagnostics := [frontend_diagnostic d]; 1
      | Ok source ->
        source_count := `Int (List.length source);
        let (al, algo_warnings) = Diagnostic.collect (fun () -> Pass.algo !inputs) in
        warnings := !warnings @ List.map frontend_diagnostic (Diagnostic.Report.to_sorted_list algo_warnings);
        match al with
        | Error d -> diagnostics := [frontend_diagnostic d]; 1
        | Ok raw_spec ->
          raw_definition_count := `Int (List.length raw_spec);
          let spec, recovered = Context.restore_empty_syntax source raw_spec in
          normalizations := recovered;
          definition_count := `Int (List.length spec);
          match Context.build ~profile:{ Coq_ir.name = !profile_name } spec with
          | Error ds -> diagnostics := ds; 1
          | Ok context ->
            mkdir !output;
            let json = match Context.to_json context with
              | `Assoc fields -> `Assoc (("source_declaration_count", !source_count) :: ("raw_al_declaration_count", !raw_definition_count) :: ("normalizations", `List !normalizations) :: fields)
              | _ -> assert false in
            write_json (Filename.concat !output "inventory.json") json;
            if !inventory then (status := "inventory-complete"; 0)
            else if !data_only then (
              match Data.lower context with
              | Error ds -> diagnostics := ds; 1
              | Ok modules ->
                let channel = open_out (Filename.concat !output "Types_0000.v") in
                (try output_string channel (Emit_data.render context modules); close_out channel
                 with exn -> close_out_noerr channel; raise exn);
                status := "data-generated"; 0)
            else (
              match Data.lower context with
              | Error ds -> diagnostics := ds; 1
              | Ok data -> match Lower_exec.lower context with
                | Error ds -> diagnostics := ds; 1
                | Ok bodies -> match Emit.write ~out_dir:!output context ~data ~bodies with
                  | Error ds -> diagnostics := ds; 1
                  | Ok () ->
                    let declarations,bindings,counts=audit_generation context data bodies in
                    let inventory=assoc_update ["stage",`String "Coq-generated";
                      "code_generation_complete",`Bool true;"coq_compiled",`Bool false;
                      "declarations",`List(List.map Context.declaration_to_json declarations);
                      "disposition_counts",counts;"builtin_bindings",`List bindings;
                      "pending_declaration_count",`Int 0;"skipped_declaration_count",`Int 0] json in
                    write_json(Filename.concat !output "inventory.json")inventory;
                    output_files := output_hashes !output;
                    if !output_files=[] then raise(Input_error(no_region,"emission produced no Coq sources"));
                    builtin_bindings := bindings; disposition_counts := counts;
                    generation_complete := true; status := "coq-generated"; 0)

    with Input_error (location, reason) -> diagnostics := [{ Coq_ir.stage = "input"; location; construct = "source-file"; reason }]; 1
    | Data.Unsupported d -> diagnostics := [d]; 1
    | exn -> diagnostics := [{ Coq_ir.stage = "frontend"; location = no_region;
      construct = "exception"; reason = Printexc.to_string exn }]; 1
  in
  List.iter report !warnings;
  List.iter report !diagnostics;
  write_json !manifest_path (`Assoc ["schema_version", `Int 1;
    "profile", `String !profile_name; "status", `String !status;
    "frontend_entrypoint", `String "Pass.algo";
    "translation_complete", `Bool false;
    "code_generation_complete", `Bool !generation_complete;
    "coq_compiled", `Bool false;
    "completion_contract", `String "translation_complete requires successful driver Coq compilation";
    "disposition_counts", !disposition_counts;
    "builtin_bindings", `List !builtin_bindings;
    "builtin_binding_count", `Int(List.length !builtin_bindings);
    "output_files", `List !output_files;
    "inputs", `List !files; "source_declaration_count", !source_count;
    "al_declaration_count", !definition_count;
    "raw_al_declaration_count", !raw_definition_count;
    "normalizations", `List !normalizations;
    "diagnostics", `List (List.map Coq_ir.diagnostic_to_json !diagnostics);
    "warnings", `List (List.map Coq_ir.diagnostic_to_json !warnings)]);
  result

let () = exit (run ())
