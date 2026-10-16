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
    | TypD {synid; tparams; deftyp} -> Some (synid.it, (tparams, deftyp.it)) | _ -> None) spec in
  let rec substitute bindings t =
    match t with
    | VarT {synid; targs = []} when List.mem_assoc synid.it bindings -> List.assoc synid.it bindings
    | VarT {synid; targs} -> VarT {synid; targs = List.map (substitute_phrase bindings) targs}
    | TupleT ts -> TupleT (List.map (substitute_phrase bindings) ts)
    | IterT {typ; iter} -> IterT {typ = substitute_phrase bindings typ; iter}
    | t -> t
  and substitute_phrase bindings t = {t with it = substitute bindings t.it} in
  let definition synid targs =
    let params, definition = List.assoc synid.it types in
    let bindings = List.map2 (fun p t -> p.it, t.it) params targs in
    bindings, definition in
  let rec value t json = match t, json with
    | NumT `IntT, `Int n -> Value.int (Bigint.of_int n)
    | NumT `NatT, `Int n -> Value.nat (Bigint.of_int n)
    | BoolT, `Bool b -> Value.bool b
    | TextT, `String s -> Value.text s
    | TupleT ts, `List vs -> Value.Make.tuple t (List.map2 (fun t j -> value t.it j) ts vs)
    | IterT {typ; iter = List}, `List vs -> Value.Make.list t (List.map (value typ.it) vs)
    | IterT {iter = Opt; _}, `Null -> Value.Make.opt t None
    | IterT {typ; iter = Opt}, `Assoc ["some", j] -> Value.Make.opt t (Some (value typ.it j))
    | VarT {synid; targs}, _ -> (let bindings, definition = definition synid targs in
      let sub t = substitute bindings t.it in
      match definition with
      | PlainT t -> value (sub t) json
      | VariantT cases ->
        let index = Yojson.Basic.Util.(json |> member "case" |> to_int) in
        let args = Yojson.Basic.Util.(json |> member "args" |> to_list) in
        let notation = (List.nth cases index).notation.it in
        let values = List.map2 (fun t j -> value (sub t) j) (Mixfix.args notation) args in
        Value.Make.case t (Mixfix.fill (Mixfix.to_mixop notation) values)
      | StructT fields ->
        Value.Make.record t (List.map (fun (a,t) ->
          a, value (sub t) (Yojson.Basic.Util.member (Lang.Xl.Atom.to_string a.it) json)) fields))
    | _ -> failwith "unsupported oracle input" in
  let rec variant_cases = function
    | VarT {synid; targs} ->
      let bindings, def = definition synid targs in
      (match def with VariantT cases -> cases
      | PlainT t -> variant_cases (substitute bindings t.it)
      | _ -> failwith "oracle variant type is not a variant")
    | _ -> failwith "oracle variant has no named type" in
  let rec json value = match value.it with
    | NumV n -> `Int (Bigint.to_int_exn (Lang.Xl.Num.to_int n))
    | BoolV b -> `Bool b | TextV s -> `String s
    | StructV fs -> `Assoc (List.map (fun (a,v) -> Lang.Xl.Atom.to_string a.it, json v) fs)
    | TupleV vs | ListV vs -> `List (List.map json vs)
    | OptV None -> `Null
    | OptV (Some v) -> `Assoc ["some", json v]
    | CaseV notation ->
      let cases = variant_cases value.note.typ in
      let rec index i = function
        | [] -> failwith "oracle variant constructor missing"
        | c :: cs -> if Mixfix.eq_mixop c.notation.it notation then i else index (i + 1) cs in
      `Assoc ["case", `Int (index 0 cases); "args", `List (List.map json (Mixfix.args notation))]
    | _ -> failwith "unsupported oracle output" in
  let relation = List.find_map (fun d -> match d.it with
    | RelD {relid; reltyp; _} when relid.it = Sys.argv.(2) -> Some reltyp | _ -> None) spec |> Option.get in
  let args = Yojson.Basic.from_string Sys.argv.(3) |> Yojson.Basic.Util.to_list in
  let args = List.map2 (fun t j -> value t.it j) (Mode.inputs relation.it) args in
  let outcome = Array.length Sys.argv > 4 && Sys.argv.(4) = "--outcome" in
  let print j = print_endline (Yojson.Basic.to_string j) in
  try match Eval_il.run (module EmptyTarget) spec Sys.argv.(2) args "<translator-test>" with
  | Ok (_, values) ->
      let values = `List (List.map json values) in
      print (if outcome then `Assoc ["status", `String "success"; "values", values] else values)
  | Error error ->
      if outcome then print (`Assoc ["status", `String (match error with
        | Eval_il.Backtrack _ -> "unmatch" | Eval_il.Plain _ -> "abort")])
      else (prerr_endline (Diag.Render.render_bag ~ansi:Diag.Ansi.plain
        (Diag.Bag.singleton (Eval_il.error_to_diagnostic error))); exit 2)
  with Assert_failure _ as error ->
    if outcome then print (`Assoc ["status", `String "exception"])
    else raise error
