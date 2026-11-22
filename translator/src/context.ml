open Util.Source
open Lang
module String_map = Map.Make(String)

type signature = {
  type_parameters : Al.tparam list;
  parameters : Al.param list;
  argument_types : Al.typ list;
  input_hint : int list option;
  input_positions : int list;
  output_positions : int list;
  output_types : Al.typ list;
}

type declaration = {
  ordinal : int;
  source_name : string;
  generated_name : string;
  namespace : string;
  kind : string;
  location : region;
  signature : signature option;
  disposition : string;
  definition : Al.def;
}

type t = {
  profile : Coq_ir.profile;
  spec : Al.spec;
  declarations : declaration list;
  by_key : declaration String_map.t;
  by_generated_name : declaration String_map.t;
  variable_metadata : declaration list;
  constructs : (string * int) list;
}

let key namespace name = namespace ^ ":" ^ name
let find t ~namespace name = String_map.find_opt (key namespace name) t.by_key

(* Namespace prefixes and byte escaping make the mapping deterministic and
   injective, including Coq keywords and source identifiers containing '_'. *)
let generated_name (profile : Coq_ir.profile) namespace name =
  let encode value =
    let b = Buffer.create (String.length value) in
    String.iter (fun c -> match c with
      | 'a'..'z' | 'A'..'Z' | '0'..'9' -> Buffer.add_char b c
      | _ -> Buffer.add_string b (Printf.sprintf "_x%02x_" (Char.code c))) value;
    Buffer.contents b
  in
  "g_" ^ encode profile.Coq_ir.name ^ "_" ^ namespace ^ "_" ^ encode name

let function_signature tparams params result =
  let argument_types = List.map (fun p -> match p.it with
    | Il.ExpP typ -> typ
    | Il.DefP (_, ts, ps, typ) ->
        let rec param_type p = match p.it with
          | Il.ExpP t -> t
          | Il.DefP (_, ts, ps, t) -> Il.FuncT (ts, List.map param_type ps, t) $ p.at
        in Il.FuncT (ts, List.map param_type ps, typ) $ p.at) params in
  { type_parameters = tparams; parameters = params; argument_types;
    input_hint = None; input_positions = List.init (List.length params) Fun.id;
    (* A function has one result even when that result is unit or a tuple. *)
    output_positions = [List.length params]; output_types = [result] }

let relation_signature typ inputs =
  let _, argument_types = Domain.Mixfix.split typ.it in
  let positions = List.init (List.length argument_types) Fun.id in
  let output_positions = List.filter (fun i -> not (List.mem i inputs)) positions in
  { type_parameters = []; parameters = []; argument_types;
    input_hint = Some inputs; input_positions = List.filter (fun i -> List.mem i inputs) positions;
    output_positions; output_types = List.map (List.nth argument_types) output_positions }

(* Exhaustive traversal of the actual AL, including inserted checks and all
   paths. Counts are AST occurrences, not an assertion of lowering support. *)
let construct_inventory spec =
  let counts = Hashtbl.create 100 in
  let hit k = Hashtbl.replace counts k (1 + Option.value ~default:0 (Hashtbl.find_opt counts k)) in
  let rec typ t = match t.it with
    | Il.BoolT -> hit "BoolT"
    | Il.NumT _ -> hit "NumT"
    | Il.TextT -> hit "TextT"
    | Il.VarT (_, ts) -> hit "VarT"; List.iter typ ts
    | Il.TupleT ts -> hit "TupleT"; List.iter typ ts
    | Il.IterT (t, _) -> hit "IterT"; typ t
    | Il.FuncT (_, ts, t) -> hit "FuncT"; List.iter typ ts; typ t
  and nottyp t = let _, ts = Domain.Mixfix.split t.it in List.iter typ ts
  and deftyp t = match t.it with
    | Il.PlainT t -> hit "PlainT"; typ t
    | Il.StructT fs -> hit "StructT"; List.iter (fun (_, t) -> typ t) fs
    | Il.VariantT cs -> hit "VariantT"; List.iter (fun (t, origin, _) -> nottyp t; List.iter typ (snd origin.it)) cs
  and param p = match p.it with
    | Il.ExpP t -> hit "ExpP"; typ t
    | Il.DefP (_, _, ps, t) -> hit "DefP"; List.iter param ps; typ t
  and arg a = match a.it with
    | Il.ExpA e -> hit "ExpA"; exp e
    | Il.DefA _ -> hit "DefA"
  and subcheck = function
    | Il.SkipSC -> hit "SkipSC"
    | Il.MixopSC _ -> hit "MixopSC"
    | Il.TupleSC ss -> hit "TupleSC"; List.iter subcheck ss
    | Il.IterSC (_, s) -> hit "IterSC"; subcheck s
    | Il.RecurseSC t -> hit "RecurseSC"; typ t
  and exp e =
    match e.it with
    | Il.BoolE _ -> hit "BoolE"
    | Il.NumE _ -> hit "NumE"
    | Il.TextE _ -> hit "TextE"
    | Il.VarE _ -> hit "VarE"
    | Il.UnE (_, _, e) -> hit "UnE"; exp e
    | Il.BinE (_, _, a, b) -> hit "BinE"; exp a; exp b
    | Il.CmpE (_, _, a, b) -> hit "CmpE"; exp a; exp b
    | Il.UpCastE (t, e) -> hit "UpCastE"; typ t; exp e
    | Il.DownCastE (t, e) -> hit "DownCastE"; typ t; exp e
    | Il.SubE (e, t, s) -> hit "SubE"; exp e; typ t; subcheck s
    | Il.MatchE (e, p) -> hit "MatchE"; exp e; (match p with
        | Il.CaseP _ -> hit "CaseP" | Il.ListP _ -> hit "ListP" | Il.OptP _ -> hit "OptP")
    | Il.TupleE es -> hit "TupleE"; List.iter exp es
    | Il.CaseE e -> hit "CaseE"; notexp e
    | Il.StrE fs -> hit "StrE"; List.iter (fun (_, e) -> exp e) fs
    | Il.OptE e -> hit "OptE"; Option.iter exp e
    | Il.ListE es -> hit "ListE"; List.iter exp es
    | Il.ConsE (a, b) -> hit "ConsE"; exp a; exp b
    | Il.CatE (a, b) -> hit "CatE"; exp a; exp b
    | Il.MemE (a, b) -> hit "MemE"; exp a; exp b
    | Il.LenE e -> hit "LenE"; exp e
    | Il.DotE (e, _) -> hit "DotE"; exp e
    | Il.IdxE (a, b) -> hit "IdxE"; exp a; exp b
    | Il.SliceE (e, a, b) -> hit "SliceE"; exp e; exp a; exp b
    | Il.UpdE (e, p, e') -> hit "UpdE"; exp e; path p; exp e'
    | Il.CallE (_, ts, args) -> hit "CallE"; List.iter typ ts; List.iter arg args
    | Il.IterE (e, (_, vars)) -> hit "IterE"; exp e; List.iter var vars
  and var (_, t, _) = hit "IterationVariable"; typ t
  and notexp e = let _, es = Domain.Mixfix.split e in List.iter exp es
  and path p = match p.it with
    | Il.RootP -> hit "RootP"
    | Il.IdxP (p, e) -> hit "IdxP"; path p; exp e
    | Il.SliceP (p, a, b) -> hit "SliceP"; path p; exp a; exp b
    | Il.DotP (p, _) -> hit "DotP"; path p
  and prem p = match p.it with
    | Il.RulePr (_, e, _) -> hit "RulePr"; notexp e
    | Il.IfPr e -> hit "IfPr"; exp e
    | Il.IfHoldPr (_, e) -> hit "IfHoldPr"; notexp e
    | Il.IfNotHoldPr (_, e) -> hit "IfNotHoldPr"; notexp e
    | Il.LetPr (a, b) -> hit "LetPr"; exp a; exp b
    | Il.IterPr (p, (_, a, b)) -> hit "IterPr"; prem p; List.iter var a; List.iter var b
    | Il.DebugPr e -> hit "DebugPr"; exp e
  and clause c = hit "Clause"; let args, e, ps = c.it in List.iter arg args; exp e; List.iter prem ps
  and rulematch (sig_, inputs, ps) = hit "RuleMatch"; List.iter exp sig_; List.iter exp inputs; List.iter prem ps
  and rulepath (_, ps, es) = hit "RulePath"; List.iter prem ps; List.iter exp es
  in
  List.iter (fun d -> match d.it with
    | Al.ExternTypD _ -> hit "ExternTypD"
    | Al.TypD (_, _, t, _) -> hit "TypD"; deftyp t
    | Al.VarD (_, t, _) -> hit "VarD"; typ t
    | Al.ExternRelD (_, t, _, _) -> hit "ExternRelD"; nottyp t
    | Al.RelD (_, t, _, gs, other, _) -> hit "RelD"; nottyp t;
        List.iter (fun g -> hit "RuleGroup"; let _, m, ps = g.it in rulematch m; List.iter rulepath ps) gs;
        Option.iter (fun g -> hit "ElseGroup"; let _, m, p = g.it in rulematch m; rulepath p) other
    | Al.ExternDecD (_, _, ps, t, _) -> hit "ExternDecD"; List.iter param ps; typ t
    | Al.BuiltinDecD (_, _, ps, t, _) -> hit "BuiltinDecD"; List.iter param ps; typ t
    | Al.TableDecD (_, ps, t, rows, _) -> hit "TableDecD"; List.iter param ps; typ t;
        List.iter (fun r -> hit "TableRow"; let es, args, e, ps = r.it in List.iter exp es; List.iter arg args; exp e; List.iter prem ps) rows
    | Al.FuncDecD (_, _, ps, t, cs, other, _) -> hit "FuncDecD"; List.iter param ps; typ t;
        List.iter clause cs; Option.iter (fun c -> hit "ElseClause"; clause c) other) spec;
  Hashtbl.to_seq counts |> List.of_seq |> List.sort (fun (a, _) (b, _) -> String.compare a b)

(* The frontend warns and omits ordinary forward syntax declarations with no
   definition. The approved Coq model gives such syntax the empty variant, while
   extern syntax remains a distinct singleton. Recover only this source case;
   never replace a failed explicit definition or an unknown referenced name. *)
let restore_empty_syntax (source : El.spec) (spec : Al.spec) =
  let existing = List.filter_map (fun d -> match d.it with
    | Al.TypD (id, _, _, _) | Al.ExternTypD (id, _) -> Some id.it
    | _ -> None) spec in
  let defined = List.filter_map (fun d -> match d.it with
    | El.TypD (id, _, _, _) | El.ExternSynD (id, _) -> Some id.it
    | _ -> None) source in
  let seen = ref (existing @ defined) in
  let restored = ref [] in
  let normalizations = ref [] in
  List.iter (fun d -> match d.it with
    | El.SynD declarations -> List.iter (fun (id, tparams) ->
        if not (List.mem id.it !seen) then (
          seen := id.it :: !seen;
          restored := (Al.TypD (id, tparams, Il.VariantT [] $ id.at, []) $ id.at) :: !restored;
          normalizations := `Assoc ["kind", `String "ordinary-empty-syntax";
            "source_name", `String id.it; "location", region_to_yojson id.at;
            "type_parameters", `List (List.map (fun t -> `String t.it) tparams);
            "representation", `String "TypD(VariantT[])";
            "reason", `String "ordinary syntax declared without a definition; omitted by original frontend"] :: !normalizations)) declarations
    | _ -> ()) source;
  spec @ List.rev !restored, List.rev !normalizations

let build ~(profile : Coq_ir.profile) spec =
  let by_key = ref String_map.empty in
  let diagnostics = ref [] in
  let declarations = List.mapi (fun ordinal definition ->
    let id, namespace, kind, signature = match definition.it with
      | Al.ExternTypD (id, _) -> id, "type", "ExternTypD", None
      | Al.TypD (id, _, _, _) -> id, "type", "TypD", None
      | Al.VarD (id, _, _) -> id, "var", "VarD", None
      | Al.ExternRelD (id, t, inputs, _) -> id, "rel", "ExternRelD", Some (relation_signature t inputs)
      | Al.RelD (id, t, inputs, _, _, _) -> id, "rel", "RelD", Some (relation_signature t inputs)
      | Al.ExternDecD (id, ts, ps, t, _) -> id, "dec", "ExternDecD", Some (function_signature ts ps t)
      | Al.BuiltinDecD (id, ts, ps, t, _) -> id, "dec", "BuiltinDecD", Some (function_signature ts ps t)
      | Al.TableDecD (id, ps, t, _, _) -> id, "dec", "TableDecD", Some (function_signature [] ps t)
      | Al.FuncDecD (id, ts, ps, t, _, _, _) -> id, "dec", "FuncDecD", Some (function_signature ts ps t)
    in
    let d = { ordinal; source_name = id.it; generated_name = generated_name profile namespace id.it;
              namespace; kind; location = definition.at; signature;
              disposition = (if namespace = "var" then "consumed-metadata" else "indexed-pending-lowering"); definition } in
    let k = key namespace id.it in
    if String_map.mem k !by_key then diagnostics := {
      Coq_ir.stage = "context"; location = definition.at; construct = kind;
      reason = "duplicate AL declaration in namespace " ^ namespace ^ ": " ^ id.it } :: !diagnostics
    else by_key := String_map.add k d !by_key;
    d) spec in
  if !diagnostics <> [] then Error (List.rev !diagnostics)
  else Ok { profile; spec; declarations; by_key = !by_key;
    by_generated_name = List.fold_left (fun acc d -> String_map.add d.generated_name d acc) String_map.empty declarations;
    variable_metadata = List.filter (fun d -> d.namespace = "var") declarations;
    constructs = construct_inventory spec }

let signature_to_json s =
  let positions xs = `List (List.map (fun i -> `Int i) xs) in
  let types xs = `List (List.map (fun t -> `String (Al.Print.string_of_typ t)) xs) in
  `Assoc ["type_parameters", `List (List.map (fun t -> `String t.it) s.type_parameters);
    "parameters", `List (List.map (fun p -> `String (Al.Print.string_of_param p)) s.parameters);
    "argument_types", types s.argument_types;
    "input_hint", (match s.input_hint with None -> `Null | Some xs -> positions xs);
    "input_positions", positions s.input_positions;
    "output_positions", positions s.output_positions; "output_types", types s.output_types;
    "output_shape", `String (match s.output_types with [] -> "unit-no-outputs" | [_] -> "single" | _ -> "multiple")]

let declaration_to_json d =
  `Assoc ["ordinal", `Int d.ordinal; "source_name", `String d.source_name;
    "generated_name", `String d.generated_name; "namespace", `String d.namespace;
    "kind", `String d.kind; "location", region_to_yojson d.location;
    "disposition", `String d.disposition;
    "signature", (match d.signature with None -> `Null | Some s -> signature_to_json s)]

(* Callback schemas preserve lexical quantification, rather than guessing an
   instantiation from a particular builtin name. DefA occurrences include local
   callback references; the declaration index tells consumers which are global. *)
let callback_inventory t =
  let schemas = ref [] in
  let strings xs = `List (List.map (fun s -> `String s) xs) in
  let unique xs = List.sort_uniq String.compare xs in
  let rec free_type bound typ = match typ.it with
    | Il.VarT (id, ts) -> (if List.mem id.it bound then [] else [id.it]) @ List.concat_map (free_type bound) ts
    | Il.TupleT ts -> List.concat_map (free_type bound) ts
    | Il.IterT (typ, _) -> free_type bound typ
    | Il.FuncT (ts, args, result) ->
        let bound = List.map it ts @ bound in List.concat_map (free_type bound) (result :: args)
    | Il.BoolT | Il.NumT _ | Il.TextT -> []
  in
  let rec free_param bound p = match p.it with
    | Il.ExpP typ -> free_type bound typ
    | Il.DefP (_, ts, ps, result) ->
        let bound = List.map it ts @ bound in
        free_type bound result @ List.concat_map (free_param bound) ps
  in
  let record d path location ambient bound inputs result free kind =
    let free = unique (List.filter (fun name -> List.mem name ambient) free) in
    schemas := `Assoc ["owner", `String d.source_name; "path", `String path;
      "kind", `String kind; "location", region_to_yojson location;
      "enclosing_type_parameters", strings ambient; "bound_type_parameters", strings bound;
      "free_type_parameters", strings free; "inputs", strings inputs;
      "result", `String (Al.Print.string_of_typ result)] :: !schemas
  in
  let rec visit_type d ambient path typ = match typ.it with
    | Il.FuncT (ts, args, result) ->
        let bound = List.map it ts in
        record d path typ.at ambient bound (List.map Al.Print.string_of_typ args) result
          (List.concat_map (free_type bound) (result :: args)) "FuncT";
        List.iteri (fun i arg -> visit_type d (ambient @ bound) (path ^ ".arg" ^ string_of_int i) arg) args;
        visit_type d (ambient @ bound) (path ^ ".result") result
    | Il.VarT (_, ts) | Il.TupleT ts -> List.iteri (fun i typ -> visit_type d ambient (path ^ ".type" ^ string_of_int i) typ) ts
    | Il.IterT (typ, _) -> visit_type d ambient (path ^ ".element") typ
    | Il.BoolT | Il.NumT _ | Il.TextT -> ()
  and visit_param d ambient path p = match p.it with
    | Il.ExpP typ -> visit_type d ambient path typ
    | Il.DefP (id, ts, ps, result) ->
        let bound = List.map it ts in
        record d (path ^ ":" ^ id.it) p.at ambient bound (List.map Al.Print.string_of_param ps) result
          (free_type bound result @ List.concat_map (free_param bound) ps) "DefP";
        List.iteri (fun i p -> visit_param d (ambient @ bound) (path ^ ".arg" ^ string_of_int i) p) ps;
        visit_type d (ambient @ bound) (path ^ ".result") result
  in
  List.iter (fun d -> match d.signature with
    | None -> (match d.definition.it with
        | Al.TypD (_, ts, deftyp, _) ->
            let ambient = List.map it ts in
            (match deftyp.it with
             | Il.PlainT typ -> visit_type d ambient "alias" typ
             | Il.StructT fs -> List.iteri (fun i (_, typ) -> visit_type d ambient ("field" ^ string_of_int i) typ) fs
             | Il.VariantT cs -> List.iteri (fun i (nt, _, _) ->
                 List.iteri (fun j typ -> visit_type d ambient (Printf.sprintf "case%d.arg%d" i j) typ) (Domain.Mixfix.args nt.it)) cs)
        | Al.VarD (_, typ, _) -> visit_type d [] "metadata" typ
        | _ -> ())
    | Some signature ->
        let ambient = List.map it signature.type_parameters in
        List.iteri (fun i p -> visit_param d ambient ("param" ^ string_of_int i) p) signature.parameters;
        (* Relation inputs and outputs share the full argument type list. *)
        if signature.parameters = [] then List.iteri (fun i typ -> visit_type d ambient ("argument" ^ string_of_int i) typ) signature.argument_types;
        List.iteri (fun i typ -> visit_type d ambient ("output" ^ string_of_int i) typ) signature.output_types) t.declarations;
  List.rev !schemas

let function_reference_inventory t =
  let module C = Al.Walk.Collect in
  let base = C.make_base ~default:[] ~compose:( @ ) in
  let collect_arg c (arg : Al.arg) = match arg.it with
    | Il.DefA id -> [id]
    | Il.ExpA _ -> C.default_collect_arg c arg in
  let collector = { base with C.collect_arg } in
  let refs = ref [] in
  List.iter (fun d ->
    let add ids = List.iter (fun id -> refs := `Assoc ["owner", `String d.source_name;
      "reference", `String id.it; "location", region_to_yojson id.at;
      "global_declaration", (match find t ~namespace:"dec" id.it with None -> `Null | Some target -> `String target.generated_name)] :: !refs) ids in
    let exps es = List.iter (fun e -> add (C.collect_exp collector e)) es in
    let args xs = List.iter (fun a -> add (C.collect_arg collector a)) xs in
    let prems ps = List.iter (fun p -> add (C.collect_prem collector p)) ps in
    let clause c = let aa, e, ps = c.it in args aa; exps [e]; prems ps in
    let rulematch (ss, ii, ps) = exps ss; exps ii; prems ps in
    let rulepath (_, ps, es) = prems ps; exps es in
    match d.definition.it with
    | Al.FuncDecD (_, _, _, _, cs, other, _) -> List.iter clause cs; Option.iter clause other
    | Al.TableDecD (_, _, _, rows, _) -> List.iter (fun row -> let ss, aa, e, ps = row.it in exps ss; args aa; exps [e]; prems ps) rows
    | Al.RelD (_, _, _, groups, other, _) ->
        List.iter (fun g -> let _, m, paths = g.it in rulematch m; List.iter rulepath paths) groups;
        Option.iter (fun g -> let _, m, path = g.it in rulematch m; rulepath path) other
    | _ -> ()) t.declarations;
  List.rev !refs

let rule_group_inventory t =
  List.concat_map(fun(d:declaration)->match d.definition.it with
    | Al.RelD(_,_,_,groups,_,_) -> List.map(fun group->
        let id,(_,_,common),paths=group.it in
        `Assoc["owner",`String d.source_name;"group",`String id.it;
          "common_premise_count",`Int(List.length common);
          "common_premises",`List(List.map(fun p->`String(Al.Print.string_of_prem p))common);
          "path_count",`Int(List.length paths)])groups
    | _->[])t.declarations

let to_json t =
  `Assoc ["schema_version", `Int 1; "profile", `String t.profile.name;
    "stage", `String "AL-inventory"; "translation_complete", `Bool false;
    "declaration_count", `Int (List.length t.declarations);
    "declarations", `List (List.map declaration_to_json t.declarations);
    "consumed_metadata_count", `Int (List.length t.variable_metadata);
    "callback_schemas", `List (callback_inventory t);
    "function_references", `List (function_reference_inventory t);
    "rule_groups", `List (rule_group_inventory t);
    "construct_counts", `Assoc (List.map (fun (name, count) -> name, `Int count) t.constructs)]
