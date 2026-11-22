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
let call c =
  if c.target="#apply" then apply "ApplyReference" (List.map expression c.arguments)
  else apply (call_constructor c.target)
    (List.map Emit_data.render_type c.type_arguments @ List.map Emit_data.ops_expr c.type_arguments @ List.map expression c.arguments)
let rec action a = match a.node with
  | Primitive_action (name,args) -> apply name (List.map expression args)
  | Return e -> apply "(@Return Call _)" [expression e]
  | Invoke c -> apply "Invoke" [call c]
  | Bind (name,left,right) -> apply "Bind" [action left;par("fun " ^ binding name ^ " => " ^ action right)]
  | Guard e -> apply "(@Guard Call)" [expression e]
  | Alternatives alternatives -> apply "Alternatives" ["[" ^ String.concat "; " (List.map action alternatives) ^ "]"]
  | Unmatch -> "(@Unmatched Call " ^ Emit_data.render_type a.result ^ ")"
  | Error e -> apply "(@Raise Call _)" [e]
  | Fresh -> "(@Fresh Call)"
  | Choose t -> "(@Choose Call " ^ Emit_data.render_type t ^ ")"
  | Negate a -> apply "Negate" [action a]
  | Match (scrutinee,branches) -> par("match " ^ expression scrutinee ^ " with " ^
      String.concat " " (List.map(fun(pattern,a)->"| "^pattern^" => "^action a) branches) ^ " end")
  | Local (name,value,body) -> par("let " ^ identifier name.name ^ " := " ^ expression value ^ " in " ^ action body)
  | Traverse (name,values,body) -> apply "Traverse" [par("fun " ^ binding name ^ " => " ^ action body); expression values]

