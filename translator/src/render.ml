open Coq_ir
let par x = "(" ^ x ^ ")"
let apply f xs = if xs=[] then f else par (String.concat " " (f::List.map par xs))
let identifier name =
  "v_" ^ String.concat "" (List.init (String.length name) (fun i -> Printf.sprintf "%02x" (Char.code name.[i])))
let tuple xs = match xs with []->"tt" | [x]->x | _->par(String.concat ", " xs)
let call_constructor name = "C_" ^ name
let reference_constructor name = "Ref_" ^ name
let rec expression e =
  match e.term with
  | Variable name -> identifier name
  | Literal code -> code
  | Constructor (name,args) | Primitive (name,args) -> apply name (List.map expression args)
  | Tuple xs -> tuple (List.map expression xs)
  | Projection (e,name) -> apply name [expression e]
  | Lambda (bindings,e) -> par("fun " ^ String.concat " " (List.map binding bindings) ^ " => " ^ expression e)
  | Apply (f,args) -> apply (expression f) (List.map expression args)
  | Match_term (scrutinee,branches) -> par("match " ^ expression scrutinee ^ " with " ^
      String.concat " " (List.map (fun (pattern,e)->"| " ^ pattern ^ " => " ^ expression e) branches) ^ " end")
  | Function name -> reference_constructor name
and binding (b:binding) = par(identifier b.name ^ " : " ^ Emit_data.render_type b.typ)
