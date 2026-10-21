(** AL blocks keep the compiler's generated premises beside their source
    premise. IDs are stable within the normalized property. *)
module S = Lang.Il

let obj fields = `Assoc fields
let str value = `String value

let rec identify path = function
  | `Assoc fields ->
      let fields = List.map (fun (key, value) ->
        (key, identify (path ^ "/" ^ key) value)) fields in
      if List.mem_assoc "kind" fields && List.mem_assoc "type" fields then
        obj (("id", str path) :: fields)
      else obj fields
  | `List values ->
      `List (List.mapi (fun index value ->
        identify (path ^ "/" ^ string_of_int index) value) values)
  | other -> other

let block encode encode_binding origin source_kind ((nodes, bindings) : S.prem list * (S.id * S.typ) list) =
  let primary = if source_kind = "relation" then 0 else List.length nodes - 1 in
  let scope = origin in
  let nodes = List.mapi (fun index node ->
    let fields = match encode node with
      | `Assoc fields -> fields
      | _ -> invalid_arg "property premise encoder must return an object" in
    let id = origin ^ "." ^ string_of_int index in
    let fields = match identify id (obj fields) with
      | `Assoc fields -> fields | _ -> assert false in
    obj (["id", str id;
          "origin", str origin; "scope", str scope;
          "auxiliary", `Bool (index <> primary);
          "source_index", `Int index] @ fields)) nodes in
  obj ["origin", str origin; "scope", str scope; "nodes", `List nodes;
       "bindings", `List (List.map (encode_binding origin) bindings)]
