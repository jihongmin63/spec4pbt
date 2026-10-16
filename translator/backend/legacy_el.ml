(* Only presentation hints cross the legacy backend boundary. *)
open Common.Source
module Atom = Domain.Atom
type id = string phrase
type atom = Atom.t phrase
type text = string
type exp = exp' phrase
and exp' =
  | TextE of string
  | AtomE of atom
  | SeqE of exp list
  | BrackE of atom * exp * atom
  | HoleE of [ `Next | `Num of int | `Rest | `None ]
  | FuseE of exp * exp
  | RawE of string
type hint = hint' phrase
and hint' = { hintid : id; hintexp : exp }
module Print = struct
  let string_of_atom a = Atom.string_of_atom a.it
  let string_of_text s = s
  let rec string_of_exp e = match e.it with
    | TextE s | RawE s -> s
    | AtomE a -> string_of_atom a
    | SeqE es -> String.concat " " (List.map string_of_exp es)
    | BrackE (l,e,r) -> string_of_atom l ^ string_of_exp e ^ string_of_atom r
    | HoleE `Next -> "%"
    | HoleE (`Num n) -> "%" ^ string_of_int n
    | HoleE `Rest -> "%%"
    | HoleE `None -> "!%"
    | FuseE (l,r) -> string_of_exp l ^ string_of_exp r
end
