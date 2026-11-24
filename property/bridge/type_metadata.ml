open Util.Source
open Lang
open Lang.Il
open Lang.Al

let active : spec ref = ref []
let definition spec name = List.find_opt (fun d -> match d.it with
  | TypD(id,_,_,_) | ExternTypD(id,_) -> id.it=name | _ -> false) spec
let rec normalize seen typ = match typ.it with
  | VarT(id,[]) when not(List.mem id.it seen) ->
      (match definition !active id.it with
       | Some {it=TypD(_,[],{it=PlainT rhs;_},_);_} -> normalize (id.it::seen) rhs
       | _ -> typ)
  | _ -> typ
let wire_type typ = Al.Print.string_of_typ (normalize [] typ)
let encode value =
  let b=Buffer.create(String.length value) in
  String.iter(fun c->match c with 'a'..'z'|'A'..'Z'|'0'..'9'->Buffer.add_char b c
    |_->Buffer.add_string b (Printf.sprintf "_x%02x_" (Char.code c))) value;
  Buffer.contents b
let coq_name namespace value = "g_fixture_" ^ namespace ^ "_" ^ encode value
(* Structural IDs retain atom kinds, punctuation, brackets, suffixes, and
   argument positions. Source regions and generated Coq names are excluded. *)
let atom_key atom = Yojson.Safe.to_string (Domain.Atom.to_yojson atom.it)
let rec mixop_key = function
  | Domain.Mixfix.Arg () -> "A"
  | Domain.Mixfix.Atom a -> "K(" ^ atom_key a ^ ")"
  | Domain.Mixfix.Brack(a,m,b) -> "B(" ^ atom_key a ^ "," ^ mixop_key m ^ "," ^ atom_key b ^ ")"
  | Domain.Mixfix.Infix(a,m,b) -> "I(" ^ mixop_key a ^ "," ^ atom_key m ^ "," ^ mixop_key b ^ ")"
  | Domain.Mixfix.Seq ms -> "S(" ^ String.concat "," (List.map mixop_key ms) ^ ")"
let simple_prefix mixop =
  let atom a = match a.it with
    | Domain.Atom.Keyword name -> Some name
    | Domain.Atom.Tag name -> Some("_" ^ name)
    | _ -> None in
  match mixop with
  | Domain.Mixfix.Atom a -> atom a
  | Domain.Mixfix.Seq(Domain.Mixfix.Atom a :: args)
    when List.for_all(function Domain.Mixfix.Arg()->true|_->false)args -> atom a
  | _ -> None
let constructor_token ?(cases=[]) mixop =
  match simple_prefix mixop with
  | Some name when List.length(List.filter(fun other->simple_prefix other=Some name)cases)<=1 -> name
  | _ -> "mixfix:" ^ mixop_key mixop
let variant_mixops name =
  let typ = normalize [] (VarT(name $ no_region,[]) $ no_region) in
  match typ.it with
  | VarT(id,[]) ->
      (match definition !active id.it with
       | Some {it=TypD(_,[],{it=VariantT cases;_},_);_} ->
           Some(List.map(fun(nottyp,_,_)->fst(Domain.Mixfix.split nottyp.it))cases)
       | _ -> None)
  | _ -> None
let mixop_of_constructor name constructor =
  match variant_mixops name with
  | None -> None
  | Some cases ->
      (match List.find_opt(fun mixop->constructor_token ~cases mixop=constructor)cases with
       | Some mixop -> Some mixop
       | None -> failwith("unknown " ^ name ^ " constructor: " ^ constructor))
let constructor_of_mixop name mixop =
  let cases=Option.value ~default:[] (variant_mixops name) in
  constructor_token ~cases mixop
let schema spec =
  List.filter_map(fun d->match d.it with
    | TypD(id,[],{it=VariantT cases;_},_) ->
        let mixops=List.map(fun(nottyp,_,_)->fst(Domain.Mixfix.split nottyp.it))cases in
        let constructors=List.mapi(fun index (nottyp,_,_)->
          let mixop,fields=Domain.Mixfix.split nottyp.it in
          `Assoc["name",`String(constructor_token ~cases:mixops mixop);
            "coq_name",`String(coq_name "case" (id.it ^ ":" ^ string_of_int index));
            "fields",`List(List.map(fun t->`String(wire_type t))fields)])cases in
        Some(id.it,`Assoc["coq_type",`String(coq_name "type" id.it);
                          "constructors",`List constructors])
    |_->None)spec |> fun fields -> `Assoc fields
