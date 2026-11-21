(* One call to the artifact's extracted theorem checker is one outer attempt. *)
open Theorem

let state seed = {
  maxSuccessTests = 1; maxDiscardedTests = 1; maxShrinkNo = 0;
  computeSize = (fun _ _ -> 2); numSuccessTests = 0;
  numDiscardedTests = 0; labels = Map.empty; expectedFailure = false;
  randomSeed0 = seed; numSuccessShrinks = 0; numTryShrinks = 0;
  stDoAnalysis = false
}

let small = MkSmallResult (None, true, [], false, [], None)

let callback_string cb st =
  match cb with
  | PostFinalFailure (_, f) | PostTest (_, f) -> ignore (f st small)

let capture callbacks st =
  let path = Filename.temp_file ~temp_dir:"." "cedar-callback-" ".raw" in
  let fd = Unix.openfile path [Unix.O_RDWR; Unix.O_TRUNC] 0o600 in
  let saved = Unix.dup Unix.stdout in
  let offsets = ref [] in
  (try
     flush stdout;
     Unix.dup2 fd Unix.stdout;
     List.iter (fun cb ->
       let first = Unix.lseek fd 0 Unix.SEEK_CUR in
       callback_string cb st;
       let last = Unix.lseek fd 0 Unix.SEEK_CUR in
       offsets := (first, last) :: !offsets) callbacks;
     flush stdout;
     Unix.dup2 saved Unix.stdout
   with exn ->
     Unix.dup2 saved Unix.stdout;
     Unix.close saved;
     Unix.close fd;
     raise exn);
  Unix.close saved;
  let channel = open_in_bin path in
  let raw = really_input_string channel (in_channel_length channel) in
  close_in channel;
  Unix.close fd;
  Sys.remove path;
  List.rev_map (fun (first, last) -> String.sub raw first (last - first)) !offsets

let json_string s =
  print_char '"';
  String.iter (fun c -> match c with
    | '"' -> print_string "\\\""
    | '\\' -> print_string "\\\\"
    | c when Char.code c < 32 || Char.code c > 126 ->
        Printf.printf "\\u%04x" (Char.code c)
    | c -> print_char c) s;
  print_char '"'

let json_fields fields =
  print_char '[';
  List.iteri (fun i field ->
    if i > 0 then print_char ',';
    json_string field) fields;
  print_char ']'

let () =
  if Array.length Sys.argv <> 4 then
    failwith "usage: sampler SEED ATTEMPTS EXPECTED_FIELDS";
  let seed_number = int_of_string Sys.argv.(1) in
  let attempts = int_of_string Sys.argv.(2) in
  let expected_fields = int_of_string Sys.argv.(3) in
  if attempts <= 0 || expected_fields <= 0 then invalid_arg "positive counts required";
  let seed = Random.State.make [|seed_number|] in
  for i = 0 to attempts - 1 do
    let MkRose (result, _) = run (theorem 2) 2 seed in
    let fields = capture result.callbacks (state seed) in
    let status = match result.ok with
      | None -> "discard"
      | Some false -> "failure"
      | Some true when List.length fields = expected_fields -> "generated"
      | Some true -> "incomplete" in
    Printf.printf "{\"attempt\":%d,\"seed\":%d,\"status\":\"%s\",\"fields\":"
      i seed_number status;
    json_fields fields;
    print_endline "}";
    if status = "failure" || status = "incomplete" then exit 2
  done
