let get = function Ok x -> x | Error e -> failwith
  (Diag.Render.render_bag ~ansi:Diag.Ansi.plain (Pass.error_to_diagnostics e))
let () =
  let namespace = ref "" and output = ref "" and manifest = ref "" and sources = ref [] in
  let options = ["--namespace",Arg.Set_string namespace,"Lean namespace";
    "--output",Arg.Set_string output,"Fresh Lean output path";
    "--manifest",Arg.Set_string manifest,"Fresh JSON manifest path"] in
  try
    Arg.parse options (fun p -> sources := !sources @ [p]) "spectec-lean --namespace NAME --output FILE --manifest FILE SPEC...";
    if !namespace = "" || !output = "" || !manifest = "" || !sources = [] then failwith "all options and at least one source are required";
    let valid_part s = String.length s > 0 && (match s.[0] with 'A'..'Z'|'a'..'z' -> true|_ -> false) &&
      String.for_all (function 'A'..'Z'|'a'..'z'|'0'..'9'|'_' -> true|_ -> false) s in
    if not (List.for_all valid_part (String.split_on_char '.' !namespace)) then failwith "invalid Lean namespace";
    if !output = !manifest || Sys.file_exists !output || Sys.file_exists !manifest then failwith "output destinations must be distinct and fresh";
    let il = get (Pass.parse_files !sources) |> Pass.elaborate |> get in
    let spec = Adapter.translate il in
    let lean = Emit.lean !namespace spec in
    let json = Yojson.Basic.pretty_to_string (Emit.manifest !namespace spec) ^ "\n" in
    let write path contents = let channel = open_out_gen [Open_wronly;Open_creat;Open_excl] 0o644 path in
      Fun.protect ~finally:(fun () -> close_out channel) (fun () -> output_string channel contents) in
    write !output lean;
    (try write !manifest json with e -> Sys.remove !output; raise e)
  with
  | Ir.Unsupported message -> prerr_endline ("unsupported SpecTecX fragment: " ^ message); exit 2
  | Failure message | Sys_error message -> prerr_endline message; exit 2
