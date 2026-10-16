(** Independent test oracle: invoke the pinned upstream IL interpreter directly.
    This module never imports the translator's adapter, IR or emitter. *)
open Common.Source
open Lang.Il
module EmptyTarget = struct
  let builtins = []
  let with_state f = f ()
  let is_impure_func _ = false
  let is_impure_rel _ = false
  let state_version = ref 0
end
let get = function Ok x -> x | Error e -> failwith
  (Diag.Render.render_bag ~ansi:Diag.Ansi.plain (Pass.error_to_diagnostics e))
let () =
  let spec = Pass.parse_files [Sys.argv.(1)] |> get |> Pass.elaborate |> get in
  let types = List.filter_map (fun d -> match d.it with
    | TypD {synid; deftyp; _} -> Some (synid.it, deftyp.it) | _ -> None) spec in
  let rec value t json = match t, json with
    | NumT `IntT, `Int n -> Value.int (Bigint.of_int n)
    | NumT `NatT, `Int n -> Value.nat (Bigint.of_int n)
    | BoolT, `Bool b -> Value.bool b
    | TextT, `String s -> Value.text s
    | VarT {synid; _}, _ -> (match List.assoc synid.it types with
      | PlainT t -> value t.it json
      | VariantT cases ->
        let index = Yojson.Basic.Util.(json |> member "case" |> to_int) in
        let args = Yojson.Basic.Util.(json |> member "args" |> to_list) in
        let notation = (List.nth cases index).notation.it in
        let values = List.map2 (fun t j -> value t.it j) (Mixfix.args notation) args in
        Value.Make.case t (Mixfix.fill (Mixfix.to_mixop notation) values)
      | StructT fields ->
        Value.Make.record t (List.map (fun (a,t) ->
          a, value t.it (Yojson.Basic.Util.member (Lang.Xl.Atom.to_string a.it) json)) fields))
    | _ -> failwith "unsupported oracle input" in
  let rec json value = match value.it with
    | NumV n -> `Int (Bigint.to_int_exn (Lang.Xl.Num.to_int n))
    | BoolV b -> `Bool b | TextV s -> `String s
    | StructV fs -> `Assoc (List.map (fun (a,v) -> Lang.Xl.Atom.to_string a.it, json v) fs)
    | _ -> failwith "unsupported oracle output" in
  let relation = List.find_map (fun d -> match d.it with
    | RelD {relid; reltyp; _} when relid.it = Sys.argv.(2) -> Some reltyp | _ -> None) spec |> Option.get in
  let args = Yojson.Basic.from_string Sys.argv.(3) |> Yojson.Basic.Util.to_list in
  let args = List.map2 (fun t j -> value t.it j) (Mode.inputs relation.it) args in
  match Eval_il.run (module EmptyTarget) spec Sys.argv.(2) args "<translator-test>" with
  | Ok (_, values) -> print_endline (Yojson.Basic.to_string (`List (List.map json values)))
  | Error error -> prerr_endline (Diag.Render.render_bag ~ansi:Diag.Ansi.plain
      (Diag.Bag.singleton (Eval_il.error_to_diagnostic error))); exit 2
