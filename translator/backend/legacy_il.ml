module El = Legacy_el
module Hints = Legacy_hints
open Domain
open Xl
module Atom = Domain.Atom
open Util.Source

[@@@ocamlformat "disable"]

(* Numbers *)

type num = Num.t

(* Texts *)

type text = string

(* Identifiers *)

type id = id' phrase
and id' = string

(* Atoms *)

type atom = atom' phrase
and atom' = Atom.t

(* Mixfix operators *)

type mixop = Mixfix.mixop

(* Iterators *)

type iter =
  | Opt       (* `?` *)
  | List      (* `*` *)

(* Variables *)

type var = id * typ * iter list

(* Types *)

and typ = typ' phrase
and typ' =
  | BoolT                                 (* `bool` *)
  | NumT of Num.typ                       (* numtyp *)
  | TextT                                 (* `text` *)
  | VarT of id * targ list                (* id (`<` list(targ, `,`) `>`)? *)
  | TupleT of typ list                    (* `(` list(typ, `,`) `)` *)
  | IterT of typ * iter                   (* typ iter *)
  | FuncT of tparam list * typ list * typ (* `<` list(tparam, `,`) `>` `(` list(typ, `,`) `)` `:` typ *)

(* Defined types *)

and nottyp = nottyp' phrase
and nottyp' = typ Mixfix.t

and deftyp = deftyp' phrase
and deftyp' =
  | PlainT of typ
  | StructT of typfield list
  | VariantT of typcase list

and typfield = atom * typ
and typorigin = typorigin' phrase
and typorigin' = id * targ list
and typcase = nottyp * typorigin * hint list

(* Values *)

(* Invariant: vid is a globally unique identifier.
   Consequently, equal vids imply structural equality. Breaking this invariant
   would cause silent bugs in the implementation of value equality, since it
   would cause id aliasing between structurally distinct values. *)

and vid = int
and vnote = { vid : vid; typ : typ'; vhash : int }

and value = (value', vnote) note_phrase
and value' =
  | BoolV of bool
  | NumV of Num.t
  | TextV of string
  | StructV of valuefield list
  | CaseV of valuecase
  | TupleV of value list
  | OptV of value option
  | ListV of value list
  | FuncV of id
  | ExternV of Yojson.Safe.t

and valuefield = atom * value
and valuecase = value Mixfix.t

(* Operators *)

and numop = [ `DecOp | `HexOp ]
and unop = [ Bool.unop | Num.unop ]
and binop = [ Bool.binop | Num.binop ]
and cmpop = [ Bool.cmpop | Num.cmpop ]
and optyp = [ Bool.typ | Num.typ ]

(* Subtype checks *)

and subcheck =
  | SkipSC
  | MixopSC of mixop list
  | TupleSC of subcheck list
  | IterSC of iter * subcheck
  | RecurseSC of typ

(* Expressions *)

and exp = (exp', typ') note_phrase
and exp' =
  | BoolE of bool                         (* bool *)
  | NumE of num                           (* num *)
  | TextE of text                         (* text *)
  | VarE of id                            (* varid *)
  | UnE of unop * optyp * exp             (* unop exp *)
  | BinE of binop * optyp * exp * exp     (* exp binop exp *)
  | CmpE of cmpop * optyp * exp * exp     (* exp cmpop exp *)
  | UpCastE of typ * exp                  (* exp as typ *)
  | DownCastE of typ * exp                (* exp as typ *)
  | SubE of exp * typ * subcheck          (* exp `<:` typ *)
  | MatchE of exp * pattern               (* exp `matches` pattern *)
  | TupleE of exp list                    (* `(` exp* `)` *)
  | CaseE of notexp                       (* notexp *)
  | StrE of (atom * exp) list             (* { expfield* } *)
  | OptE of exp option                    (* exp? *)
  | ListE of exp list                     (* `[` exp* `]` *)
  | ConsE of exp * exp                    (* exp `::` exp *)
  | CatE of exp * exp                     (* exp `++` exp *)
  | MemE of exp * exp                     (* exp `<-` exp *)
  | LenE of exp                           (* `|` exp `|` *)
  | DotE of exp * atom                    (* exp.atom *)
  | IdxE of exp * exp                     (* exp `[` exp `]` *)
  | SliceE of exp * exp * exp             (* exp `[` exp `:` exp `]` *)
  | UpdE of exp * path * exp              (* exp `[` path `=` exp `]` *)
  | CallE of id * targ list * arg list    (* $id`<` targ* `>``(` arg* `)` *)
  | IterE of exp * iterexp                (* exp iterexp *)

and notexp = exp Mixfix.t
and iterexp = iter * var list

(* Patterns *)

and pattern =
  | CaseP of mixop
  | ListP of [ `Cons | `Fixed of int | `Nil ]
  | OptP of [ `Some | `None ]

(* Path *)

and path = (path', typ') note_phrase
and path' =
  | RootP                        (*  *)
  | IdxP of path * exp           (* path `[` exp `]` *)
  | SliceP of path * exp * exp   (* path `[` exp `:` exp `]` *)
  | DotP of path * atom          (* path `.` atom *)

(* Parameters *)

and param = param' phrase
and param' =
  (* typ *)
  | ExpP of typ
  (* `def` `$`id ` (`<` list(tparam, `,`) `>`)? (`(` list(param, `,`) `)`)? `:` typ *)
  | DefP of id * tparam list * param list * typ

(* Type parameters *)

and tparam = tparam' phrase
and tparam' = id'

(* Arguments *)

and arg = arg' phrase
and arg' =
  | ExpA of exp   (* exp *)
  | DefA of id    (* `$`id *)

(* Type arguments *)

and targ = targ' phrase
and targ' = typ'

(* Premises *)

and prem = prem' phrase
and prem' =
  | RulePr of id * notexp * Hints.Input.t (* id `:` notexp *)
  | IfPr of exp                           (* `if` exp *)
  | IfHoldPr of id * notexp               (* `if` id `:` notexp `holds` *)
  | IfNotHoldPr of id * notexp            (* `if` id `:` notexp `does not hold` *)
  | LetPr of exp * exp                    (* `let` exp `=` exp *)
  | IterPr of prem * iterprem             (* prem iterprem *)
  | DebugPr of exp                        (* `debug` exp *)

and iterprem = iter * var list * var list

(* Rules *)

and rule = rule' phrase
and rule' = id * notexp * prem list

and rulegroup = rulegroup' phrase
and rulegroup' = id * rule list

and elsegroup = elsegroup' phrase
and elsegroup' = id * rule

(* Clauses *)

and clause = clause' phrase
and clause' = arg list * exp * prem list

and elseclause = clause
and elseclause' = clause'

(* Table rows *)

and tablerow = tablerow' phrase
and tablerow' = arg list * exp

(* Hints *)

and hint = El.hint

(* Definitions *)

type def = def' phrase
and def' =
  (* `extern` `syntax` id hint* *)
  | ExternTypD of id * hint list
  (* `syntax` id `<` list(tparam, `,`) `>` hint* `=` deftyp *)
  | TypD of id * tparam list * deftyp * hint list
  (* `var` id `:` typ hint* *)
  | VarD of id * typ * hint list
  (* `extern` `relation` id `:` nottyp `hint(input` `%`int* `)` hint* *)
  | ExternRelD of id * nottyp * Hints.Input.t * hint list
  (* `relation` id `:` nottyp `hint(input` `%`int* `)` rulegroup* hint* *)
  | RelD of id * nottyp * Hints.Input.t * rulegroup list * elsegroup option * hint list
  (* `extern` `dec` id `<` list(tparam, `,`) `>` list(param, `,`) `:` typ hint* *)
  | ExternDecD of id * tparam list * param list * typ * hint list
  (* `builtin` `dec` id `<` list(tparam, `,`) `>` list(param, `,`) `:` typ hint* *)
  | BuiltinDecD of id * tparam list * param list * typ * hint list
  (* `table` `dec` id list(param, `,`) `:` typ hint* *)
  | TableDecD of id * param list * typ * tablerow list * hint list
  (* `dec` id `<` list(tparam, `,`) `>` list(param, `,`) `:` typ clause* hint* *)
  | FuncDecD of id * tparam list * param list * typ * clause list * elseclause option * hint list

(* Spec *)

type spec = def list

module Free = struct
open Domain.Lib
module Mixfix = Domain.Mixfix
open Util.Source

(* Identifier set *)

type t = IdSet.t

let empty = IdSet.empty
let singleton = IdSet.singleton
let ( + ) = IdSet.union

(* Collect free identifiers *)

(* Expressions *)

let rec free_exp (exp : exp) : t =
  match exp.it with
  | BoolE _ | NumE _ | TextE _ -> empty
  | VarE id -> singleton id
  | UnE (_, _, exp) -> free_exp exp
  | BinE (_, _, exp_l, exp_r) -> free_exp exp_l + free_exp exp_r
  | CmpE (_, _, exp_l, exp_r) -> free_exp exp_l + free_exp exp_r
  | UpCastE (_, exp) -> free_exp exp
  | DownCastE (_, exp) -> free_exp exp
  | SubE (exp, _, _) -> free_exp exp
  | MatchE (exp, _) -> free_exp exp
  | TupleE exps -> free_exps exps
  | CaseE notexp -> free_exps (Mixfix.args notexp)
  | StrE expfields -> expfields |> List.map snd |> free_exps
  | OptE (Some exp) -> free_exp exp
  | OptE None -> empty
  | ListE exps -> free_exps exps
  | ConsE (exp_h, exp_t) -> free_exp exp_h + free_exp exp_t
  | CatE (exp_l, exp_r) -> free_exp exp_l + free_exp exp_r
  | MemE (exp_e, exp_s) -> free_exp exp_e + free_exp exp_s
  | LenE exp -> free_exp exp
  | DotE (exp, _) -> free_exp exp
  | IdxE (exp_b, exp_i) -> free_exp exp_b + free_exp exp_i
  | SliceE (exp_b, exp_l, exp_h) ->
      free_exp exp_b + free_exp exp_l + free_exp exp_h
  | UpdE (exp_b, path, exp_f) ->
      free_exp exp_b + free_path path + free_exp exp_f
  | CallE (_, _, args) -> free_args args
  | IterE (exp, _) -> free_exp exp

and free_exps (exps : exp list) : t =
  exps |> List.map free_exp |> List.fold_left ( + ) empty

(* Paths *)

and free_path (path : path) : t =
  match path.it with
  | RootP -> empty
  | IdxP (path, exp) -> free_path path + free_exp exp
  | SliceP (path, exp_l, exp_h) ->
      free_path path + free_exp exp_l + free_exp exp_h
  | DotP (path, _) -> free_path path

(* Arguments *)

and free_arg (arg : arg) : t =
  match arg.it with ExpA exp -> free_exp exp | DefA _ -> empty

and free_args (args : arg list) : t =
  args |> List.map free_arg |> List.fold_left ( + ) empty

(* Premises *)

let rec free_prem (prem : prem) : t =
  match prem.it with
  | RulePr (_, notexp, _) -> free_exps (Mixfix.args notexp)
  | IfPr exp -> free_exp exp
  | IfHoldPr (_, notexp) -> free_exps (Mixfix.args notexp)
  | IfNotHoldPr (_, notexp) -> free_exps (Mixfix.args notexp)
  | LetPr (exp_l, exp_r) -> free_exp exp_l + free_exp exp_r
  | IterPr (prem, _) -> free_prem prem
  | DebugPr exp -> free_exp exp

and free_prems (prems : prem list) : t =
  prems |> List.map free_prem |> List.fold_left ( + ) empty

(* Rules *)

let free_rule (rule : rule) : t =
  let _, notexp, prems = rule.it in
  free_exps (Mixfix.args notexp) + free_prems prems

let free_rules (rules : rule list) : t =
  rules |> List.map free_rule |> List.fold_left ( + ) empty

let free_rulegroup (rulegroup : rulegroup) : t =
  let _, rules = rulegroup.it in
  free_rules rules

let free_rulegroups (rulegroups : rulegroup list) : t =
  rulegroups |> List.map free_rulegroup |> List.fold_left ( + ) empty

let free_elsegroup (elsegroup : elsegroup) : t =
  let _, rule = elsegroup.it in
  free_rule rule

let free_elsegroup_opt (elsegroup_opt : elsegroup option) : t =
  match elsegroup_opt with
  | Some elsegroup -> free_elsegroup elsegroup
  | None -> empty

(* Clauses *)

let free_clause (clause : clause) : t =
  let args, exp, prems = clause.it in
  free_args args + free_exp exp + free_prems prems

let free_clauses (clauses : clause list) : t =
  clauses |> List.map free_clause |> List.fold_left ( + ) empty

let free_elseclause (elseclause : elseclause) : t = free_clause elseclause

let free_elseclause_opt (elseclause_opt : elseclause option) : t =
  match elseclause_opt with
  | Some elseclause -> free_elseclause elseclause
  | None -> empty

(* Table rows *)

let free_tablerow (tablerow : tablerow) : t =
  let args, exp = tablerow.it in
  free_args args + free_exp exp

let free_tablerows (tablerows : tablerow list) : t =
  tablerows |> List.map free_tablerow |> List.fold_left ( + ) empty

(* Definitions *)

let free_def (def : def) : t =
  match def.it with
  | RelD (_, _, _, rulegroups, elsegroup_opt, _) ->
      free_rulegroups rulegroups + free_elsegroup_opt elsegroup_opt
  | TableDecD (_, _, _, tablerows, _) -> free_tablerows tablerows
  | FuncDecD (_, _, _, _, clauses, elseclause_opt, _) ->
      free_clauses clauses + free_elseclause_opt elseclause_opt
  | _ -> empty

end

module Print = struct
module Mixfix = Domain.Mixfix
open Xl
module Atom = Domain.Atom
open Util.Print
open Util.Source

(* Numbers *)

let string_of_num = Num.string_of_num

(* Texts *)

let string_of_text text = text

(* Identifiers *)

let string_of_varid varid = varid.it
let string_of_typid typid = typid.it
let string_of_relid relid = relid.it
let string_of_ruleid ruleid = ruleid.it
let string_of_rulegroupid rulegroupid = rulegroupid.it
let string_of_defid defid = "$" ^ defid.it

(* Atoms *)

let string_of_atom atom = Atom.string_of_atom atom.it

let string_of_atoms atoms =
  match atoms with
  | [] -> ""
  | _ -> atoms |> List.map string_of_atom |> String.concat ""

(* Mixfix operators *)

let string_of_mixop mixop = Mixfix.to_string mixop

(* Iterators *)

let string_of_iter iter = match iter with Opt -> "?" | List -> "*"

(* Variables *)

let string_of_var (id, _typ, iters) =
  string_of_varid id ^ String.concat "" (List.map string_of_iter iters)

(* Types *)

let rec string_of_typ typ =
  match typ.it with
  | BoolT -> "bool"
  | NumT numtyp -> Num.string_of_typ numtyp
  | TextT -> "text"
  | VarT (typid, targs) -> string_of_typid typid ^ string_of_targs targs
  | TupleT typs -> "(" ^ string_of_typs ", " typs ^ ")"
  | IterT (typ, iter) -> string_of_typ typ ^ string_of_iter iter
  | FuncT (tparams, typs, typ) ->
      string_of_tparams tparams ^ "(" ^ string_of_typs ", " typs ^ ") : "
      ^ string_of_typ typ

and string_of_typs sep typs = String.concat sep (List.map string_of_typ typs)

and string_of_nottyp nottyp =
  Mixfix.render ~string_of_atom ~string_of_arg:string_of_typ nottyp.it

and string_of_deftyp deftyp =
  match deftyp.it with
  | PlainT typ -> string_of_typ typ
  | StructT typfields -> "{" ^ string_of_typfields ", " typfields ^ "}"
  | VariantT typcases -> "\n   | " ^ string_of_typcases "\n   | " typcases

and string_of_typfield typfield =
  let atom, typ = typfield in
  string_of_atom atom ^ " " ^ string_of_typ typ

and string_of_typfields sep typfields =
  String.concat sep (List.map string_of_typfield typfields)

and string_of_typorigin typorigin =
  let id, targs = typorigin.it in
  "(from " ^ string_of_typid id ^ string_of_targs targs ^ ")"

and string_of_typcase typcase =
  let nottyp, typorigin, hints = typcase in
  string_of_nottyp nottyp ^ " "
  ^ string_of_typorigin typorigin
  ^ " " ^ string_of_hints hints

and string_of_typcases sep typcases =
  String.concat sep (List.map string_of_typcase typcases)

(* Values *)

and string_of_value ?(short = false) ?(level = 0) value =
  match value.it with
  | BoolV b -> string_of_bool b
  | NumV n -> string_of_num n
  | TextV s -> String.escaped s
  | StructV [] -> "{}"
  | StructV valuefields when short ->
      Format.asprintf "{ .../%d }" (List.length valuefields)
  | StructV valuefields ->
      Format.sprintf "{\n%s\n%s}"
        (String.concat ";\n"
           (List.map
              (fun (atom, value) ->
                let indent = indent (level + 1) in
                Format.asprintf "%s%s %s" indent (string_of_atom atom)
                  (string_of_value ~short ~level:(level + 1) value))
              valuefields))
        (indent level)
  | CaseV valuecase when short -> string_of_mixop (Mixfix.to_mixop valuecase)
  | CaseV valuecase -> string_of_notval ~level valuecase
  | TupleV values ->
      Format.asprintf "(%s)"
        (String.concat ", "
           (List.map (string_of_value ~short ~level:(level + 1)) values))
  | OptV (Some value) ->
      Format.asprintf "Some(%s)"
        (string_of_value ~short ~level:(level + 1) value)
  | OptV None -> "None"
  | ListV [] -> "[]"
  | ListV values when short -> Format.asprintf "[ .../%d ]" (List.length values)
  | ListV values ->
      Format.asprintf "[\n%s\n%s]"
        (String.concat ",\n"
           (List.map
              (fun value ->
                let indent = indent (level + 1) in
                indent ^ string_of_value ~short ~level:(level + 1) value)
              values))
        (indent level)
  | FuncV id -> string_of_defid id
  | ExternV _ -> "extern"

and string_of_notval ?(level = 0) notval =
  Mixfix.render ~string_of_atom
    ~string_of_arg:(string_of_value ~level:(level + 1))
    notval

(* Operators *)

and string_of_unop = function
  | #Bool.unop as op -> Bool.string_of_unop op
  | #Num.unop as op -> Num.string_of_unop op

and string_of_binop = function
  | #Bool.binop as op -> Bool.string_of_binop op
  | #Num.binop as op -> Num.string_of_binop op

and string_of_cmpop = function
  | #Bool.cmpop as op -> Bool.string_of_cmpop op
  | #Num.cmpop as op -> Num.string_of_cmpop op

(* Expressions *)

and string_of_exp exp =
  match exp.it with
  | BoolE b -> string_of_bool b
  | NumE n -> string_of_num n
  | TextE text -> "\"" ^ String.escaped text ^ "\""
  | VarE varid -> string_of_varid varid
  | UnE (unop, _, exp) -> string_of_unop unop ^ string_of_exp exp
  | BinE (binop, _, exp_l, exp_r) ->
      "(" ^ string_of_exp exp_l ^ " " ^ string_of_binop binop ^ " "
      ^ string_of_exp exp_r ^ ")"
  | CmpE (cmpop, _, exp_l, exp_r) ->
      "(" ^ string_of_exp exp_l ^ " " ^ string_of_cmpop cmpop ^ " "
      ^ string_of_exp exp_r ^ ")"
  | UpCastE (typ, exp) -> string_of_exp exp ^ " as " ^ string_of_typ typ
  | DownCastE (typ, exp) -> string_of_exp exp ^ " as " ^ string_of_typ typ
  | SubE (exp, typ, _) -> string_of_exp exp ^ " <: " ^ string_of_typ typ
  | MatchE (exp, pattern) ->
      string_of_exp exp ^ " matches " ^ string_of_pattern pattern
  | TupleE es -> "(" ^ string_of_exps ", " es ^ ")"
  | CaseE notexp -> string_of_notexp notexp
  | StrE expfields ->
      "{"
      ^ String.concat ", "
          (List.map
             (fun (atom, exp) -> string_of_atom atom ^ " " ^ string_of_exp exp)
             expfields)
      ^ "}"
  | OptE exp_opt -> "?(" ^ string_of_exps "" (Option.to_list exp_opt) ^ ")"
  | ListE exps -> "[" ^ string_of_exps ", " exps ^ "]"
  | ConsE (exp_h, exp_t) -> string_of_exp exp_h ^ " :: " ^ string_of_exp exp_t
  | CatE (exp_l, exp_r) -> string_of_exp exp_l ^ " ++ " ^ string_of_exp exp_r
  | MemE (exp_e, exp_s) -> string_of_exp exp_e ^ " <- " ^ string_of_exp exp_s
  | LenE exp -> "|" ^ string_of_exp exp ^ "|"
  | DotE (exp_b, atom) -> string_of_exp exp_b ^ "." ^ string_of_atom atom
  | IdxE (exp_b, exp_i) -> string_of_exp exp_b ^ "[" ^ string_of_exp exp_i ^ "]"
  | SliceE (exp_b, exp_l, exp_h) ->
      string_of_exp exp_b ^ "[" ^ string_of_exp exp_l ^ " : "
      ^ string_of_exp exp_h ^ "]"
  | UpdE (exp_b, path, exp_f) ->
      string_of_exp exp_b ^ "[" ^ string_of_path path ^ " = "
      ^ string_of_exp exp_f ^ "]"
  | CallE (defid, targs, args) ->
      string_of_defid defid ^ string_of_targs targs ^ string_of_args args
  | IterE (exp, iterexp) -> string_of_exp exp ^ string_of_iterexp iterexp

and string_of_exps sep exps = String.concat sep (List.map string_of_exp exps)

and string_of_notexp notexp =
  Mixfix.render ~string_of_atom ~string_of_arg:string_of_exp notexp

and string_of_iterexp iterexp =
  let iter, vars = iterexp in
  string_of_iter iter ^ "{"
  ^ String.concat ", "
      (List.map
         (fun var ->
           let id, typ, iters = var in
           string_of_var var ^ " <- " ^ string_of_var (id, typ, iters @ [ iter ]))
         vars)
  ^ "}"

and string_of_iterexps iterexps =
  iterexps |> List.map string_of_iterexp |> String.concat ""

(* Patterns *)

and string_of_pattern pattern =
  match pattern with
  | CaseP mixop -> string_of_mixop mixop
  | ListP `Cons -> "_ :: _"
  | ListP (`Fixed len) -> Format.asprintf "[ _/%d ]" len
  | ListP `Nil -> "[]"
  | OptP `Some -> "(_)"
  | OptP `None -> "()"

(* Paths *)

and string_of_path path =
  match path.it with
  | RootP -> ""
  | IdxP (path, exp) -> string_of_path path ^ "[" ^ string_of_exp exp ^ "]"
  | SliceP (path, exp_l, exp_h) ->
      string_of_path path ^ "[" ^ string_of_exp exp_l ^ " : "
      ^ string_of_exp exp_h ^ "]"
  | DotP ({ it = RootP; _ }, atom) -> string_of_atom atom
  | DotP (path, atom) -> string_of_path path ^ "." ^ string_of_atom atom

(* Parameters *)

and string_of_param param =
  match param.it with
  | ExpP typ -> string_of_typ typ
  | DefP (defid, tparams, params, typ) ->
      string_of_defid defid ^ string_of_tparams tparams
      ^ string_of_params params ^ " : " ^ string_of_typ typ

and string_of_params params =
  match params with
  | [] -> ""
  | params -> "(" ^ String.concat ", " (List.map string_of_param params) ^ ")"

(* Type parameters *)

and string_of_tparam tparam = tparam.it

and string_of_tparams tparams =
  match tparams with
  | [] -> ""
  | tparams ->
      "<" ^ String.concat ", " (List.map string_of_tparam tparams) ^ ">"

(* Arguments *)

and string_of_arg arg =
  match arg.it with
  | ExpA exp -> string_of_exp exp
  | DefA defid -> string_of_defid defid

and string_of_args args =
  match args with
  | [] -> ""
  | args -> "(" ^ String.concat ", " (List.map string_of_arg args) ^ ")"

(* Type arguments *)

and string_of_targ targ = string_of_typ targ

and string_of_targs targs =
  match targs with
  | [] -> ""
  | targs -> "<" ^ String.concat ", " (List.map string_of_targ targs) ^ ">"

(* Premises *)

and string_of_prem prem =
  match prem.it with
  | RulePr (id, notexp, _inputs) ->
      string_of_relid id ^ ": " ^ string_of_notexp notexp
  | IfPr exp -> "if " ^ string_of_exp exp
  | IfHoldPr (id, notexp) ->
      "if " ^ string_of_relid id ^ ": " ^ string_of_notexp notexp ^ " holds"
  | IfNotHoldPr (id, notexp) ->
      "if " ^ string_of_relid id ^ ": " ^ string_of_notexp notexp
      ^ " does not hold"
  | LetPr (exp_l, exp_r) ->
      "let " ^ string_of_exp exp_l ^ " = " ^ string_of_exp exp_r
  | IterPr (({ it = IterPr _; _ } as prem), iterprem) ->
      string_of_prem prem ^ string_of_iterprem iterprem
  | IterPr (prem, iterprem) ->
      "(" ^ string_of_prem prem ^ ")" ^ string_of_iterprem iterprem
  | DebugPr exp -> "debug " ^ string_of_exp exp

and string_of_prems ?(level = 0) prems =
  let indent = indent level in
  String.concat ""
    (List.map (fun prem -> "\n" ^ indent ^ "-- " ^ string_of_prem prem) prems)

and string_of_iterprem iterprem =
  let iter, vars_bound, vars_bind = iterprem in
  string_of_iter iter ^ "{"
  ^ String.concat ", "
      (List.map
         (fun var ->
           let id, typ, iters = var in
           string_of_var var ^ " <- " ^ string_of_var (id, typ, iters @ [ iter ]))
         vars_bound
      @ List.map
          (fun var ->
            let id, typ, iters = var in
            string_of_var var ^ " -> "
            ^ string_of_var (id, typ, iters @ [ iter ]))
          vars_bind)
  ^ "}"

and string_of_iterprems iterprems =
  iterprems |> List.map string_of_iterprem |> String.concat ""

(* Rules *)
and string_of_rule rule =
  let ruleid, notexp, prems = rule.it in
  "rule " ^ string_of_ruleid ruleid ^ ": " ^ string_of_notexp notexp
  ^ string_of_prems ~level:2 prems

and string_of_rules rules =
  String.concat ""
    (List.map (fun rule -> "\n\n" ^ indent 2 ^ string_of_rule rule) rules)

and string_of_rulegroup rulegroup =
  let rulegroupid, rules = rulegroup.it in
  indent 1 ^ "rulegroup "
  ^ string_of_rulegroupid rulegroupid
  ^ string_of_rules rules

and string_of_rulegroups rulegroups =
  rulegroups |> List.map string_of_rulegroup |> String.concat "\n\n"

and string_of_elsegroup elsegroup =
  let elsegroupid, rule = elsegroup.it in
  indent 1 ^ "rulegroup "
  ^ string_of_rulegroupid elsegroupid
  ^ string_of_rules [ rule ]

and string_of_elsegroup_opt elsegroup_opt =
  match elsegroup_opt with
  | None -> ""
  | Some elsegroup ->
      "\n\n" ^ indent 1 ^ "elsegroup\n\n" ^ string_of_elsegroup elsegroup

(* Clause *)

and string_of_clause idx clause =
  let args, exp, prems = clause.it in
  "clause " ^ string_of_int idx ^ " : " ^ string_of_args args ^ " = "
  ^ string_of_exp exp
  ^ string_of_prems ~level:1 prems

and string_of_clauses clauses =
  String.concat ""
    (List.mapi
       (fun idx clause -> "\n\n" ^ indent 1 ^ string_of_clause idx clause)
       clauses)

and string_of_elseclause elseclause = string_of_clause (-1) elseclause

and string_of_elseclause_opt elseclause_opt =
  match elseclause_opt with
  | None -> ""
  | Some elseclause -> "\n\n" ^ indent 1 ^ string_of_elseclause elseclause

(* Table rows *)

and string_of_tablerow tablerow =
  let args, exp = tablerow.it in
  "\n" ^ indent 2 ^ string_of_args args ^ " -> " ^ string_of_exp exp

and string_of_tablerows tablerows =
  String.concat ""
    (List.mapi
       (fun idx tablerow ->
         "\n" ^ indent 1 ^ "row " ^ string_of_int idx ^ " :"
         ^ string_of_tablerow tablerow)
       tablerows)

(* Hints *)

and string_of_hint hint =
  " hint(" ^ hint.it.El.hintid.it ^ " "
  ^ El.Print.string_of_exp hint.it.hintexp
  ^ ")"

and string_of_hints hints = String.concat "" (List.map string_of_hint hints)

(* Definitions *)

let rec string_of_def def =
  match def.it with
  | ExternTypD (id, _) -> "extern syntax " ^ string_of_typid id
  | TypD (typid, tparams, deftyp, _) ->
      "syntax " ^ string_of_typid typid ^ string_of_tparams tparams ^ " = "
      ^ string_of_deftyp deftyp
  | VarD (id, typ, _) -> "var " ^ string_of_varid id ^ " : " ^ string_of_typ typ
  | ExternRelD (relid, nottyp, _, _) ->
      "extern relation " ^ string_of_relid relid ^ ": "
      ^ string_of_nottyp nottyp
  | RelD (relid, nottyp, _, rulegroups, elsegroup_opt, _) ->
      "relation " ^ string_of_relid relid ^ ": " ^ string_of_nottyp nottyp
      ^ "\n\n"
      ^ string_of_rulegroups rulegroups
      ^ string_of_elsegroup_opt elsegroup_opt
  | ExternDecD (defid, tparams, params, typ, _) ->
      "extern def " ^ string_of_defid defid ^ string_of_tparams tparams
      ^ string_of_params params ^ " : " ^ string_of_typ typ
  | BuiltinDecD (defid, tparams, params, typ, _) ->
      "builtin def " ^ string_of_defid defid ^ string_of_tparams tparams
      ^ string_of_params params ^ " : " ^ string_of_typ typ
  | TableDecD (defid, params, typ, tablerows, _) ->
      "tbl def " ^ string_of_defid defid ^ string_of_params params ^ " : "
      ^ string_of_typ typ ^ " ="
      ^ string_of_tablerows tablerows
  | FuncDecD (defid, tparams, params, typ, clauses, elseclause_opt, _) ->
      "def " ^ string_of_defid defid ^ string_of_tparams tparams
      ^ string_of_params params ^ " : " ^ string_of_typ typ ^ " ="
      ^ string_of_clauses clauses
      ^ string_of_elseclause_opt elseclause_opt

and string_of_defs defs = String.concat "\n\n" (List.map string_of_def defs)

(* Spec *)

let string_of_spec spec = string_of_defs spec

end
