module Run = Runtime.Dynamic_Runner.Signature
module V = Runtime.Value
module T = Runtime.Type.Typ
module External = struct
  module Cache = struct let cache_on () = () let cache_off () = () end
  let eval_extern_rel _ _ = failwith "unexpected extern relation"
  let eval_extern_func _ _ _ = failwith "unexpected extern function"
  let checkpoint () = 0
  let seff _ _ = false
  let clear () = ()
  let init_mode _ = Ok ()
end
module Engine = Interp_al.Interp.Make (Interface.SpecTec_AL) (External) ()
let nat n = V.Make.nat (Bigint.of_int n)
let list ns = V.Make.list (T.Make.list T.Make.nat) (List.map nat ns)
let observe thunk =
  try thunk () with
  | Invalid_argument message -> "Invalid_argument:" ^ message
  | Builtin.Error.BuiltinError _ -> "BuiltinError"
let call name values () =
  match Engine.eval_func name [] values with
  | Run.Pass value -> "Pass:" ^ V.to_string value
  | Run.Fail (Run.Unmatch _) -> "Unmatch"
  | Run.Fail (Run.Abort _) -> "Abort"
let check label expected thunk =
  let actual = observe thunk in
  Printf.printf "%s: %s\n%!" label actual;
  if actual <> expected then failwith (label ^ ": expected " ^ expected)
let () =
  assert (Sys.int_size = 63);
  let spec = match Pass.algo [Sys.argv.(1)] with Ok s -> s | Error _ -> failwith "frontend" in
  (match Engine.init ~cache:false ~det:false ~guard:true spec with Ok () -> () | Error _ -> failwith "init");
  check "list slice overflow" "Pass:[]" (call "list_slice" [list [4;8]; nat max_int; nat 1]);
  check "list slice bounds" "Unmatch" (call "list_slice" [list []; nat max_int; nat 0]);
  check "text slice overflow" "Invalid_argument:String.sub / Bytes.sub"
    (call "text_slice" [V.Make.text "abc"; nat max_int; nat 1]);
  check "text slice maximum count" "Invalid_argument:String.sub / Bytes.sub"
    (call "text_slice" [V.Make.text "abc"; nat 1; nat max_int]);
  check "list update overflow" "Pass:[\n  4,\n  8\n]"
    (call "list_update" [list [4;8]; nat max_int; nat 1; list [7]]);
  check "list update length mismatch" "Unmatch"
    (call "list_update" [list [4;8]; nat max_int; nat 1; list []]);
  check "text update overflow" "Invalid_argument:String.sub / Bytes.sub"
    (call "text_update" [V.Make.text "abc"; nat max_int; nat 1; V.Make.text "x"]);
  check "text update length mismatch" "Unmatch"
    (call "text_update" [V.Make.text "abc"; nat max_int; nat 1; V.Make.text ""]);
  check "nested text slice access" "Invalid_argument:String.sub / Bytes.sub"
    (call "nested_text_update" [V.Make.text "abc"; nat max_int; nat 1; V.Make.text ""]);
  let bytes fn args () = ignore (fn ignore Util.Source.no_region [] args); "Pass" in
  check "slice_bytes overflow" "Invalid_argument:Value_array.sub"
    (bytes Native_bytes.slice_bytes [list []; nat max_int; nat 1]);
  check "slice_bytes bounds" "BuiltinError"
    (bytes Native_bytes.slice_bytes [list []; nat max_int; nat 0]);
  check "replace_bytes overflow" "Invalid_argument:Value_array.replace_slice"
    (bytes Native_bytes.replace_bytes [list []; nat max_int; list [7]]);
  check "replace_bytes bounds" "BuiltinError"
    (bytes Native_bytes.replace_bytes [list []; nat max_int; list []])
