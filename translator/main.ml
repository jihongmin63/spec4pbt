let get = function Ok x -> x | Error e -> failwith
  (Diag.Render.render_bag ~ansi:Diag.Ansi.plain (Pass.error_to_diagnostics e))
let () =
  let namespace = ref "" and output = ref "" and manifest = ref "" and sources = ref [] in
  let backend = ref "observation" and declarative = ref false and noncomputable = ref false in
  let builtin_profile = ref false in
  let options = ["--namespace",Arg.Set_string namespace,"Lean namespace";
    "--output",Arg.Set_string output,"Fresh Lean output path";
    "--manifest",Arg.Set_string manifest,"Fresh JSON manifest path (observation backend)";
    "--backend",Arg.Symbol (["observation"; "ported"], fun value -> backend := value),
      "Select observation (default) or ported donor backend";
    "--declarative",Arg.Set declarative,"Emit declarative relations (ported backend)";
    "--builtin-profile",Arg.Symbol (["donor"], fun _ -> builtin_profile := true),
      "Use the donor's builtin meanings explicitly (ported backend)";
    "--noncomputable",Arg.Set noncomputable,"Emit ordered logical plans without executable evaluation (ported backend)"] in
  try
    Arg.parse options (fun p -> sources := !sources @ [p]) "spectec-lean --namespace NAME --output FILE [--backend ported | --manifest FILE] SPEC...";
    if !namespace = "" || !output = "" || !sources = [] then
      failwith "namespace, output and at least one source are required";
    if !backend = "observation" && !manifest = "" then
      failwith "the observation backend requires --manifest";
    if !backend = "ported" && !manifest <> "" then
      failwith "the ported backend does not yet emit observation manifests; omit --manifest";
    if !backend = "observation" && (!declarative || !noncomputable || !builtin_profile) then
      failwith "--declarative, --noncomputable and --builtin-profile require --backend ported";
    if !declarative && !noncomputable then
      failwith "--declarative and --noncomputable select different output modes";
    let valid_part s = String.length s > 0 && (match s.[0] with 'A'..'Z'|'a'..'z' -> true|_ -> false) &&
      String.for_all (function 'A'..'Z'|'a'..'z'|'0'..'9'|'_' -> true|_ -> false) s &&
      not (List.mem s Lean_backend.Identifier.lean_keywords) in
    if not (List.for_all valid_part (String.split_on_char '.' !namespace)) then failwith "invalid Lean namespace";
    if !output = !manifest || Sys.file_exists !output || Sys.file_exists !manifest then failwith "output destinations must be distinct and fresh";
    let il = get (Pass.parse_files !sources) |> Pass.elaborate |> get in
    let lean, json = match !backend with
      | "observation" ->
          let spec = Adapter.translate il in
          Emit.lean !namespace spec,
          Some (Yojson.Basic.pretty_to_string (Emit.manifest !namespace spec) ^ "\n")
      | _ ->
          let source = Current_adapter.translate ~ordered:(not !declarative)
            ~builtin_profile:!builtin_profile il in
          let lean = match Lean_backend.Pipeline.transpile ~namespace:!namespace
            ~ordered:(not !declarative) ~executable:(not !noncomputable && not !declarative) source with
            | Ok lean -> lean
            | Error diagnostic -> failwith (Lean_backend.Diagnostic.render diagnostic) in
          lean, None in
    let write path contents = let channel = open_out_gen [Open_wronly;Open_creat;Open_excl] 0o644 path in
      Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel contents) in
    write !output lean;
    (match json with None -> () | Some json ->
      try write !manifest json with e -> Sys.remove !output; raise e)
  with
  | Ir.Unsupported message -> prerr_endline ("unsupported SpecTecX fragment: " ^ message); exit 2
  | Lean_backend.Translator.Unsupported_il diagnostic ->
      prerr_endline (Lean_backend.Diagnostic.render diagnostic); exit 2
  | Failure message | Sys_error message | Invalid_argument message -> prerr_endline message; exit 2
