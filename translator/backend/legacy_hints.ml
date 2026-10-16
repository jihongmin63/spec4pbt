module Input = struct
  type t = int list
let split (hint : t) (items : 'a list) : 'a list * 'a list =
  let rec go idx items_input_rev items_output_rev = function
    | [] -> (List.rev items_input_rev, List.rev items_output_rev)
    | item :: items ->
        if List.memq idx hint then
          go (idx + 1) (item :: items_input_rev) items_output_rev items
        else go (idx + 1) items_input_rev (item :: items_output_rev) items
  in
  go 0 [] [] items

let combine (hint : t) (items_input : 'a list) (items_output : 'a list) :
    'a list =
  let len = List.length items_input + List.length items_output in
  let idxs_input, idxs_output =
    List.init len Fun.id |> List.partition (fun idx -> List.memq idx hint)
  in
  let items_input_indexed = List.combine idxs_input items_input in
  let items_output_indexed = List.combine idxs_output items_output in
  items_input_indexed @ items_output_indexed
  |> List.sort (fun (idx_a, _) (idx_b, _) -> Int.compare idx_a idx_b)
  |> List.map snd


end
module Alter = struct
open Legacy_el
open Common.Source
type t =
  | TextH of text
  | AtomH of atom
  | SeqH of t list
  | BrackH of atom * t * atom
  | HoleH of [ `Next | `Num of int ] phrase
  | FuseH of t * t
  | OtherH of exp

let rec to_string (hint : t) =
  Format.asprintf "hint(alter %s)" (to_string' hint)

and to_string' (hint : t) =
  match hint with
  | TextH str -> Print.string_of_text str
  | AtomH atom -> Print.string_of_atom atom
  | SeqH hintexps -> hintexps |> List.map to_string' |> String.concat " "
  | BrackH (atom_l, hintexp, atom_r) ->
      Format.asprintf "%s %s %s"
        (Print.string_of_atom atom_l)
        (to_string' hintexp)
        (Print.string_of_atom atom_r)
  | HoleH { it = `Next; _ } -> "%"
  | HoleH { it = `Num idx; _ } -> Format.asprintf "%%%d" idx
  | FuseH (hintexp_l, hintexp_r) ->
      Format.asprintf "%s#%s" (to_string' hintexp_l) (to_string' hintexp_r)
  | OtherH exp -> Print.string_of_exp exp

(* Creating hints *)

let rec init (hintexp : exp) : t =
  match hintexp.it with
  | TextE text -> TextH text
  | AtomE atom -> AtomH atom
  | SeqE hintexps -> SeqH (List.map init hintexps)
  | BrackE (atom_l, hintexp, atom_r) -> BrackH (atom_l, init hintexp, atom_r)
  | HoleE `Next -> HoleH (`Next $ hintexp.at)
  | HoleE (`Num idx) -> HoleH (`Num idx $ hintexp.at)
  | FuseE (hintexp_l, hintexp_r) -> FuseH (init hintexp_l, init hintexp_r)
  | _ -> OtherH hintexp


end
