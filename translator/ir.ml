(** Small checked execution IR, independent of the upstream IL representation.
    Unsupported source constructs never reach emission. *)
type typ = Bool | Nat | Int | Text | Named of string
type expr = { typ : typ; node : node }
and node =
  | Var of string | Literal of string | Unary of string * expr
  | Binary of string * expr * expr | Compare of string * expr * expr
  | Constructor of string * int * expr list
  | Record of (string * expr) list | Field of expr * string
  | IsConstructor of expr * int * int | NatToInt of expr

type step = Bind of expr * expr | Guard of expr | Call of string * expr list * expr list

type rule = { inputs : expr list; outputs : expr list; steps : step list; fallback : bool }
type relation = { name : string; slots : (bool * typ) list; rules : rule list }
type typedef = RecordType of (string * typ) list | VariantType of typ list list | Alias of typ
type spec = { types : (string * typedef) list; relations : relation list }

exception Unsupported of string
let unsupported message = raise (Unsupported message)
