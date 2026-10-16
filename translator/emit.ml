open Ir

(* Reserve s_ for injective byte encoding. Ordinary source names remain
   legible unless Lean reserves them; source s_ names are encoded too. *)
let ident s =
  let reserved = ["if";"then";"else";"match";"with";"let";"in";"def";"end";
    "namespace";"structure";"inductive";"class";"instance";"where";"by";"do";
    "return";"Type";"Prop";"fun";"forall";"open";"import";"abbrev";"mutual"] in
  let safe = String.length s > 0 &&
    (match s.[0] with 'a'..'z' | 'A'..'Z' -> true | _ -> false) &&
    String.for_all (function 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> true | _ -> false) s in
  if safe && not (String.starts_with ~prefix:"s_" s) && not (List.mem s reserved) then "«" ^ s ^ "»"
  else "«s_" ^ String.concat "" (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i]))) ^ "»"
let bare s = let x = ident s in String.sub x 2 (String.length x - 4)
let var s = "v_" ^ String.concat "" (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i])))
let typ = function Bool -> "_root_.Bool" | Nat -> "_root_.Nat" | Int -> "_root_.Int" | Text -> "_root_.String" | Named n -> ident n
let typekey = function Bool -> "bool" | Nat -> "nat" | Int -> "int" | Text -> "text" | Named n -> n
let tuple = function [] -> "()" | [x] -> x | xs -> "(" ^ String.concat ", " xs ^ ")"
let tupletype = function [] -> "_root_.Unit" | xs -> String.concat " × " (List.map typ xs)
let app f args = "(" ^ String.concat " " (f :: args) ^ ")"
let quote s = Yojson.Basic.to_string (`String s)
let ctor name i = ident name ^ ".c" ^ string_of_int i
let rec expr e = match e.node with
  | Var n -> var n | Literal s -> "(" ^ s ^ " : " ^ typ e.typ ^ ")"
  | Unary (op,a) -> "(" ^ op ^ expr a ^ ")"
  | Binary (op,a,b) -> "(" ^ expr a ^ " " ^ op ^ " " ^ expr b ^ ")"
  | Compare (op,a,b) -> "(_root_.Decidable.decide (" ^ expr a ^ " " ^ op ^ " " ^ expr b ^ "))"
  | Constructor (name,i,args) -> app (ctor name i) (List.map expr args)
  | Record fields -> "({ " ^ String.concat ", " (List.map (fun (n,e) -> ident n ^ " := " ^ expr e) fields) ^ " } : " ^ typ e.typ ^ ")"
  | Field (e,n) -> "(" ^ expr e ^ ")." ^ ident n
  | IsConstructor (e,i,arity) -> "(match " ^ expr e ^ " with | .c" ^ string_of_int i ^
      String.concat "" (List.init arity (fun _ -> " _")) ^ " => true | _ => false)"
  | NatToInt e -> "(_root_.Int.ofNat " ^ expr e ^ ")"
let rec pattern e = match e.node with
  | Var n -> var n
  | Constructor (name,i,args) -> app (ctor name i) (List.map pattern args)
  | Record fields -> "{ " ^ String.concat ", " (List.map (fun (n,e) -> ident n ^ " := " ^ pattern e) fields) ^ " }"
  | _ -> unsupported "non-binding assignment pattern"
let rec irrefutable types e = match e.node with
  | Var _ -> true
  | Record fields -> List.for_all (fun (_, e) -> irrefutable types e) fields
  | Constructor (name, _, args) ->
      (match List.assoc_opt name types with Some (VariantType [_]) -> true | _ -> false)
      && List.for_all (irrefutable types) args
  | _ -> false
let mismatch types patterns =
  if List.for_all (irrefutable types) patterns then ""
  else " | _ => .abort \"IL assignment mismatch\""
let bind types pattern_exp value next =
  match pattern_exp.node with
  | Var _ -> "(let " ^ pattern pattern_exp ^ " := " ^ value ^ "; " ^ next ^ ")"
  | _ -> "(match " ^ value ^ " with | " ^ pattern pattern_exp ^ " => " ^ next ^
      mismatch types [pattern_exp] ^ ")"
let bind_outputs types outputs value next = match outputs with
  | [] -> "(let () := " ^ value ^ "; " ^ next ^ ")"
  | [p] -> bind types p value next
  | ps -> "(match " ^ value ^ " with | " ^ tuple (List.map pattern ps) ^ " => " ^ next ^ mismatch types ps ^ ")"
let rec steps types prems outputs = match prems with
  | [] -> ".pure " ^ tuple (List.map expr outputs)
  | Bind (p,e) :: rest -> bind types p (expr e) (steps types rest outputs)
  | Guard e :: rest -> ".bind (.guard (" ^ expr e ^ " = true)) (fun _ => " ^ steps types rest outputs ^ ")"
  | Call (name,ins,outs) :: rest ->
      ".bind (.call " ^ app ("Call." ^ ident name) (List.map expr ins) ^
      ") (fun callResult => " ^ bind_outputs types outs "callResult" (steps types rest outputs) ^ ")"
let rule types (r : rule) =
  List.fold_right (fun (p,i) body -> bind types p ("input" ^ string_of_int i) body)
    (List.mapi (fun i p -> p,i) r.inputs) (steps types r.steps r.outputs)
let ordered types rules = List.fold_right (fun r rest ->
    ".orElse (" ^ rule types r ^ ") (fun _ => " ^ rest ^ ")") rules ".unmatch"
let inputs r = List.filter_map (fun (i,t) -> if i then Some t else None) r.slots
let outputs r = List.filter_map (fun (i,t) -> if i then None else Some t) r.slots

let validate spec =
  let declarations = ["Call"; "program"] @ List.map fst spec.types @
    List.concat_map (fun r -> [r.name; "run" ^ r.name]) spec.relations in
  let rec unique seen = function
    | [] -> ()
    | n :: ns -> if List.mem (bare n) seen then unsupported ("generated declaration collision: " ^ n)
      else unique (bare n :: seen) ns in
  unique [] declarations;
  let check_type available = function
    | Named n when not (List.mem n available) ->
      unsupported ("type must be declared earlier (mutual recursion unsupported): " ^ n)
    | _ -> () in
  ignore (List.fold_left (fun available (name, td) ->
    (match td with
    | Alias t -> check_type available t
    | RecordType fields -> List.iter (fun (_,t) -> check_type available t) fields
    | VariantType cases -> List.iter (List.iter (check_type (name :: available))) cases);
    name :: available) [] spec.types)

let lean namespace spec =
  validate spec;
  let b = Buffer.create 8192 in
  let line s = Buffer.add_string b (s ^ "\n") in
  line "import Lean"; line "import pbt.SpectecRuntime.RunEval";
  line "set_option autoImplicit false";
  line "set_option linter.unusedVariables false";
  line ("namespace " ^ namespace); line "open SpecTecExecution";
  List.iter (fun (name,td) -> match td with
    | Alias t -> line ("abbrev " ^ ident name ^ " := " ^ typ t)
    | RecordType fields ->
      line ("structure " ^ ident name ^ " where");
      List.iter (fun (n,t) -> line ("  " ^ ident n ^ " : " ^ typ t)) fields;
      line "  deriving _root_.DecidableEq, _root_.Repr, _root_.Lean.ToJson, _root_.Lean.FromJson"
    | VariantType cases ->
      if cases = [] then unsupported "empty variant";
      line ("inductive " ^ ident name ^ " where");
      List.iteri (fun i args -> line ("  | c" ^ string_of_int i ^ " : " ^
        String.concat " → " (List.map typ args @ [ident name]))) cases;
      line "  deriving _root_.DecidableEq, _root_.Repr, _root_.Lean.ToJson, _root_.Lean.FromJson") spec.types;
  if spec.relations = [] then unsupported "specification has no relations";
  line "inductive Call : Type → Type where";
  List.iter (fun r -> line ("  | " ^ ident r.name ^ " : " ^
    String.concat " → " (List.map typ (inputs r) @ ["Call (" ^ tupletype (outputs r) ^ ")"]))) spec.relations;
  line "def program : _root_.SpecTecExecution.ExecutableProgram Call where";
  line "  primitive := fun _ _ => _root_.False";
  line "  body := fun request => match request with";
  List.iter (fun r -> line ("    | " ^ app ("Call." ^ ident r.name)
      (List.mapi (fun i _ -> "input" ^ string_of_int i) (inputs r)) ^ " =>\n      " ^ ordered spec.types r.rules)) spec.relations;
  List.iter (fun r ->
    let inargs = List.mapi (fun i t -> "(input" ^ string_of_int i ^ " : " ^ typ t ^ ")") (inputs r) in
    let call = app ("Call." ^ ident r.name) (List.mapi (fun i _ -> "input" ^ string_of_int i) (inputs r)) in
    line ("def " ^ ident ("run" ^ r.name) ^ " (fuel : _root_.Nat) " ^ String.concat " " inargs ^
      " : _root_.SpecTecExecution.RunResult (" ^ tupletype (outputs r) ^ ") :=\n  _root_.SpecTecExecution.runEval program (_root_.SpecTecExecution.PrimitiveRunner.unavailable program) fuel (.call " ^ call ^ ") 0");
    let args = List.mapi (fun i (_,t) -> "(arg" ^ string_of_int i ^ " : " ^ typ t ^ ")") r.slots in
    let slotargs want = List.filter_map (fun (i,(isinput,_)) -> if isinput = want then Some ("arg" ^ string_of_int i) else None) (List.mapi (fun i slot -> i,slot) r.slots) in
    let call = app ("Call." ^ ident r.name) (slotargs true) in
    line ("def " ^ ident r.name ^ " " ^ String.concat " " args ^ " : Prop :=\n  ∃ final, _root_.SpecTecExecution.Eval program.erase (.call ⟨_, " ^ call ^ "⟩) 0 (.success (.of " ^ tuple (slotargs false) ^ ")) final")) spec.relations;
  line ("end " ^ namespace); Buffer.contents b

let manifest namespace spec =
  let str s = `String s in
  let full n = namespace ^ "." ^ bare n in
  let prim n lean = n, `Assoc ["kind",str "primitive"; "lean",str lean] in
  let types = [prim "bool" "Bool";prim "nat" "Nat";prim "int" "Int";prim "text" "String"] @
    List.map (fun (name,td) ->
      let fields = match td with
        | RecordType fs -> ["kind",str "record";"fields",`Assoc (List.map (fun (n,t) -> n, `Assoc ["type",str (typekey t);"lean",str (bare n)]) fs)]
        | VariantType _ -> ["kind",str "variant"]
        | Alias t -> ["kind",str "alias";"type",str (typekey t)] in
      name, `Assoc (("lean",str (full name)) :: fields)) spec.types in
  let relations = List.map (fun r -> r.name, `Assoc [
    "lean",str (full r.name);
    "inputs",`List (List.filter_map (fun (index,(input,_)) -> if input then Some (`Int index) else None) (List.mapi (fun i x -> i,x) r.slots));
    "arguments",`List (List.map (fun (_,t) -> `Assoc ["type",str (typekey t)]) r.slots)]) spec.relations in
  `Assoc ["schema_version",`Int 1;"namespace",str namespace;"types",`Assoc types;"relations",`Assoc relations]
