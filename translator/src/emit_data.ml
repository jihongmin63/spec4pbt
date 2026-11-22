open Coq_ir
open Util.Source
open Lang
let par s = "(" ^ s ^ ")"
let apply f xs = if xs=[] then f else par (String.concat " " (f::List.map par xs))
let rec render_type = function
  | Unit -> "unit" | Bool -> "bool" | Nat -> "nat" | Int -> "Z" | Text -> "string"
  | Type_parameter n -> n
  | Named(n,ts) -> apply n (List.map render_type ts)
  | Product [] -> "unit" | Product [t] -> render_type t
  | Product (t::ts) -> List.fold_left(fun left right->par(left ^ " * " ^ render_type right) ^ "%type") (render_type t) ts
  | List t -> apply "list" [render_type t] | Option t -> apply "option" [render_type t]
  | Function_ref {parameters=[];inputs;output} -> apply "FunctionRef" [render_type (Product inputs);render_type output]
  | Function_ref _ -> failwith "polymorphic Function_ref requires named reference schema"
let ops_name n = n ^ "_ops"
let equal_name n = n ^ "_equal"
let compare_name n = n ^ "_compare"
let print_name n = n ^ "_print"
let unparse_name n = n ^ "_unparse"
let quote s =
  (* Coq string literals double quotes; byte escapes are OCaml-only. Build
     control/non-ASCII bytes with constructors so source text is lossless. *)
  let chunks=ref [] and b=Buffer.create 32 in
  let flush ()=if Buffer.length b>0 then (chunks := ("\"" ^ Buffer.contents b ^ "\"") :: !chunks;Buffer.clear b) in
  String.iter (fun c -> let n=Char.code c in if n>=32 && n<127 then (if c='"' then Buffer.add_string b "\"\"" else Buffer.add_char b c)
    else (flush ();chunks := Printf.sprintf "(String (ascii_of_nat %d) EmptyString)" n :: !chunks)) s;
  flush (); match List.rev !chunks with [] -> "\"\"" | x::xs -> List.fold_left (fun a b -> apply "String.append" [a;b]) x xs
let append xs = match xs with []->quote "" | x::xs -> List.fold_left (fun a b -> apply "String.append" [a;b]) x xs
let sequence xs tail = List.fold_right (fun c rest -> "match " ^ c ^ " with Eq => " ^ rest ^ " | c => c end") xs tail
let merge_optional separator expressions =
  let names=List.mapi(fun i _->"unparsed_"^string_of_int i)expressions in
  List.fold_right(fun(expr,name)tail->"match "^expr^" with None => None | Some "^name^" => "^tail^" end") (List.combine expressions names) (apply "Some" [apply "join_text" [quote separator;"["^String.concat "; " names^"]"]])
let conjunction xs = List.fold_right (fun x rest -> apply "andb" [x;rest]) xs "true"
let tuple_pattern xs = match xs with []->"tt" | [x]->x | _-> par (String.concat ", " xs)
let rec ops_expr = function
  | Unit -> "unit_ops" | Bool -> "bool_ops" | Nat -> "nat_ops" | Int -> "int_ops" | Text -> "text_ops"
  | Type_parameter n -> "ops_" ^ n
  | Named(n,ts) -> apply (ops_name n) (List.map render_type ts @ List.map ops_expr ts)
  | List t -> apply "list_ops" [ops_expr t] | Option t -> apply "option_ops" [ops_expr t]
  | Product [] -> "unit_ops"
  | Product ts ->
      let xs=List.mapi(fun i _->"tuple_a"^string_of_int i)ts and ys=List.mapi(fun i _->"tuple_b"^string_of_int i)ts in
      let eqs=List.map2(fun t (x,y)->apply "equal_value" [ops_expr t;x;y])ts(List.combine xs ys) in
      let cmps=List.map2(fun t (x,y)->apply "compare_value" [ops_expr t;x;y])ts(List.combine xs ys) in
      let printed=List.map2(fun t x->apply "print_value" [ops_expr t;"(S level)";x])ts xs in
      let unparsed=List.map2(fun t x->apply "unparse_value" [ops_expr t;x])ts xs in
      "{| equal_value := fun x y => match x, y with "^tuple_pattern xs^", "^tuple_pattern ys^" => "^conjunction eqs^" end; "^
      "compare_value := fun x y => match x, y with "^tuple_pattern xs^", "^tuple_pattern ys^" => "^sequence cmps "Eq"^" end; "^
      "print_value := fun level x => match x with "^tuple_pattern xs^" => "^append[quote "(";apply "join_text" [quote ", ";"["^String.concat "; " printed^"]"];quote ")"]^" end; "^
      "unparse_value := fun x => match x with "^tuple_pattern xs^" => match "^merge_optional ", " unparsed^" with None => None | Some text => Some "^par(append[quote "(";"text";quote ")"])^" end end |}"
  | Function_ref _ -> "function_ref_ops"
let params ps = String.concat " " (List.map (fun p -> par (p ^ " : Set")) ps)
let capabilities ps = String.concat " " (List.map (fun p -> par ("ops_" ^ p ^ " : ValueOps@{Set} " ^ p)) ps)
let instantiated n ps = apply n ps
let source ctx name = Context.String_map.find name ctx.Context.by_generated_name
let record_ctor ctx name = Data.record_constructor ctx (source ctx name).source_name
let rec replace substitutions = function
  | Type_parameter p as t -> Option.value ~default:t (List.assoc_opt p substitutions)
  | Named(n,ts)->Named(n,List.map (replace substitutions) ts)
  | List t->List(replace substitutions t) | Option t->Option(replace substitutions t)
  | Product ts->Product(List.map (replace substitutions) ts)
  | t->t
type comparison_code = Known of int | Compare_then of string * comparison_code
let rec followed_by a b = match a with Known 0 -> b | Known _ -> a | Compare_then(e,r) -> Compare_then(e, followed_by r b)
let followed_by_lazy a f = match a with Known 0 -> f () | Known _ -> a | _ -> followed_by a (f ())
let rec comparison_term = function Known n -> if n=0 then "Eq" else if n<0 then "Lt" else "Gt" | Compare_then(e,r) -> sequence [e] (comparison_term r)
let render ctx modules =
  let all=List.concat_map (fun m->m.declarations) modules in
  let data_index=Hashtbl.create 1000 in List.iter(fun d->Hashtbl.add data_index (Data.declaration_name d) d)all;
  let find n=Hashtbl.find data_index n in
  let rec expand seen = function
    | Named(n,ts) as t -> (match find n with
        | Alias(_,ps,rhs) when not(List.mem n seen) -> expand (n::seen) (replace (List.combine ps ts) rhs)
        | _->t)
    | t->t in
  let b=Buffer.create 100000 in let line s=Buffer.add_string b (s^"\n") in
  line "From Coq Require Import String Ascii List Bool ZArith Arith.";
  line "From ALCoq Require Import Values.";line "Import ListNotations.";line "Open Scope string_scope.";line "Set Universe Polymorphism.";line "Unset Implicit Arguments.";line "Unset Automatic Proposition Inductives.";line "Unset Elimination Schemes.";
  let active_names=ref [] in
  let nested_support=ref(fun _ _ _->assert false) in
  let rec contains_active typ = match expand [] typ with
    |Named(n,ts)->List.mem n !active_names || List.exists contains_active ts
    |Product ts->List.exists contains_active ts |List t|Option t->contains_active t|_->false in
  let rec support op typ args =
    let typ=expand [] typ in
    match typ,args with
    | Named(_,ts),_ when List.exists contains_active ts -> !nested_support op typ args
    | Named(n,ts),_ -> apply ((match op with `Eq->equal_name | `Cmp->compare_name | `Print->print_name | `Unparse->unparse_name) n)
        (List.map render_type ts @ List.map ops_expr ts @ args)
    | List t,[x] when op=`Unparse ->
        apply (par("fix walk (xs : list "^par(render_type t)^") : option string := match xs with [] => Some \"\" | a :: ax => match "^support `Unparse t ["a"]^" with None => None | Some text => match ax with [] => Some text | _ => match walk ax with None => None | Some rest => Some (String.append text (String.append \" \" rest)) end end end end")) [x]
    | Option t,[x] when op=`Unparse -> "match "^x^" with None => Some \"\" | Some a => "^support `Unparse t ["a"]^" end"
    | Product ts,[x] when op=`Unparse -> let xs=List.mapi(fun i _->"a"^string_of_int i)ts in
        "match "^x^" with "^tuple_pattern xs^" => match "^merge_optional ", " (List.map2(fun t a->support `Unparse t [a])ts xs)^" with None => None | Some text => Some (String.append \"(\" (String.append text \")\")) end end"
    | List t,[x;y] when op<>`Print ->
        let body = match op with
          | `Eq -> "match xs, ys with | [], [] => true | a :: ax, c :: cx => andb " ^ par (support `Eq t ["a";"c"]) ^ " (walk ax cx) | _, _ => false end"
          | `Cmp -> "match xs, ys with | [], [] => Eq | [], _ => Lt | _, [] => Gt | a :: ax, c :: cx => " ^ sequence [support `Cmp t ["a";"c"]] "(walk ax cx)" ^ " end"
          | _ -> assert false in
        apply (par ("fix walk (xs ys : list " ^ par(render_type t) ^ ") {struct xs} : " ^ (if op=`Eq then "bool" else "comparison") ^ " := " ^ body)) [x;y]
    | List t,[level;x] ->
        let element=support `Print t ["(S "^level^")";"a"] in
        let walk="(fix walk (xs : list "^par(render_type t)^") : list string := match xs with [] => [] | a :: ax => String.append (indent (S "^level^")) "^element^" :: walk ax end)" in
        "match "^x^" with [] => \"[]\" | _ => " ^ append [quote "[";"newline";apply "join_text" [append[quote ",";"newline"];apply walk [x]];"newline";apply "indent" [level];quote "]"] ^ " end"
    | Option t,[x;y] when op<>`Print -> "match "^x^", "^y^" with | None, None => "^(if op=`Eq then "true" else "Eq")^" | Some a, Some c => "^support op t ["a";"c"]^" | None, _ => "^(if op=`Eq then "false" else "Lt")^" | _, _ => "^(if op=`Eq then "false" else "Gt")^" end"
    | Option t,[l;x] when op=`Print -> "match "^x^" with None => \"None\" | Some a => "^append[quote "Some(";support `Print t ["(S "^l^")";"a"];quote ")"]^" end"
    | Product ts,[x;y] when op<>`Print ->
        let xs=List.mapi (fun i _->"a"^string_of_int i) ts and ys=List.mapi(fun i _->"c"^string_of_int i)ts in
        let cs=List.map2(fun t (a,c)->support op t [a;c])ts(List.combine xs ys) in
        "match "^x^", "^y^" with "^tuple_pattern xs^", "^tuple_pattern ys^" => "^(if op=`Eq then conjunction cs else sequence cs "Eq")^" end"
    | Product ts,[l;x] -> let xs=List.mapi(fun i _->"a"^string_of_int i)ts in
        "match "^x^" with "^tuple_pattern xs^" => " ^ append[quote "(";apply "join_text" [quote ", ";"["^String.concat "; " (List.map2(fun t a->support `Print t ["(S "^l^")";a])ts xs)^"]"];quote ")"] ^" end"
    | _,_ -> apply (match op with `Eq->"equal_value"|`Cmp->"compare_value"|`Print->"print_value"|`Unparse->"unparse_value") (ops_expr typ::args)
  in
  let constructors = function Inductive(_,_,cs)->cs | Record(n,_,fs)->[{constructor_name=record_ctor ctx n;fields=List.map(fun (f:binding)->f.typ)fs}] | _->[] in
  let pattern c prefix = let vs=List.mapi(fun i _->prefix^string_of_int i)c.fields in String.concat " " (c.constructor_name::vs),vs in
  let printer d c vars =
    let name=Data.declaration_name d in let sd=source ctx name in
    match sd.definition.it with
    | Al.ExternTypD _ -> quote "extern"
    | Al.TypD(_,_,{it=Il.StructT fs;_},_) -> if fs=[] then quote "{}" else
        append [quote "{";"newline";apply "join_text" [append[quote ";";"newline"];"["^String.concat "; " (List.map2(fun (a,_) (t,v)->append["(indent (S level))";quote (Il.Print.string_of_atom a ^ " ");support `Print t ["(S level)";v]])fs(List.combine c.fields vars))^"]"];"newline";"(indent level)";quote "}"]
    | Al.TypD(_,_,{it=Il.VariantT cs;_},_) ->
        let t,_,_=List.find(fun(t,_,_)->Data.constructor_name ctx sd.source_name (fst(Domain.Mixfix.split t.it))=c.constructor_name)cs in
        let _,types=Domain.Mixfix.split t.it in let index=ref 0 in
        let mapped=Domain.Mixfix.map (fun _ -> let i= !index in incr index;support `Print (List.nth c.fields i) ["(S level)";List.nth vars i]) t.it in
        ignore types;
        Domain.Mixfix.assemble ~empty:(quote "") ~space:(quote " ") ~atom:(fun a->let s=Il.Print.string_of_atom a in if s="" then None else Some(quote s)) ~concat:(fun a b->append[a;b]) mapped
    | _->assert false
  in
  let unparser d c vars =
    let name=Data.declaration_name d in let sd=source ctx name in
    match sd.definition.it with
    |Al.ExternTypD _|Al.TypD(_,_,{it=Il.StructT _;_},_)->"None"
    |Al.TypD(_,_,{it=Il.VariantT cs;_},_)->
      let t,_,hints=List.find(fun(t,_,_)->Data.constructor_name ctx sd.source_name(fst(Domain.Mixfix.split t.it))=c.constructor_name)cs in
      let atom a=match a.it with Domain.Atom.Tag _->""|_->String.lowercase_ascii(Domain.Atom.render_atom a.it) in
      let arguments=List.map2(fun typ value->support `Unparse typ [value])c.fields vars in
      let hint=List.find_opt(fun hint->El.(hint.it.hintid.it="print"))hints in
      (match hint with
      |Some hint->Hints.Alter.alternate ~empty:(apply "Some" [quote ""])
          ~text:(fun text->if text="" then None else Some(apply "Some" [quote text]))
          ~atom:(fun a->apply "Some" [quote(atom a)])
          ~join:(merge_optional " ") ~fuse:(fun a b->merge_optional "" [a;b])
          ~other:(fun e->apply "Some" [quote(El.Print.string_of_exp e)])
          (Hints.Alter.init El.(hint.it.hintexp)) Fun.id arguments
      |None->let index=ref 0 in
        let mapped=Domain.Mixfix.map(fun _->let i= !index in incr index;List.nth arguments i)t.it in
        Domain.Mixfix.assemble ~empty:(apply "Some" [quote ""]) ~space:(apply "Some" [quote " "])
          ~atom:(fun a->let text=atom a in if text="" then None else Some(apply "Some" [quote text]))
          ~concat:(fun a b->merge_optional "" [a;b])mapped)
    |_->assert false
  in
  let mixop_index=Hashtbl.create 1000 in
  List.iter(fun d->match (source ctx (Data.declaration_name d)).definition.it with
    |Al.TypD(_,_,{it=Il.VariantT cs;_},_)->List.iter(fun(t,_,_)->let mixop,_=Domain.Mixfix.split t.it in
      Hashtbl.add mixop_index (Data.constructor_name ctx (source ctx(Data.declaration_name d)).source_name mixop) mixop)cs
    |_->())all;
  let mixop_of_constructor _ c = Hashtbl.find_opt mixop_index c.constructor_name in
  let source_tag typ = match expand [] typ with
    | Bool->0 | Nat|Int->1 | Text->2 | Product _|Unit->5 | Option _->6 | List _->8 | Function_ref _->9
    | Named(n,_)->(match (source ctx n).definition.it with Al.ExternTypD _->10 | Al.TypD(_,_,{it=Il.StructT _;_},_)->3 | _->4)
    | Type_parameter _-> -1 in
  let cross_requests = ref [] in
  let rec free_parameters = function
    | Type_parameter p -> [p]
    | Named(_,ts)|Product ts -> List.concat_map free_parameters ts
    | List t|Option t -> free_parameters t
    | _ -> [] in
  let cross_parameters t u = List.sort_uniq String.compare (free_parameters t @ free_parameters u) in
  let request_cross t u =
    match List.find_opt(fun(t0,u0,_)->t=t0 && u=u0) !cross_requests with
    |Some(_,_,name)->name
    |None->let name=Context.generated_name ctx.Context.profile "cross" (string_of_int(List.length !cross_requests)) in
        cross_requests := !cross_requests @ [t,u,name];name in
  let rec cross t a u c =
    let t=expand [] t and u=expand [] u in
    if t=u then support `Cmp t [a;c]
    else match t,u with
      | Nat,Int -> "Lt"
      | Int,Nat -> "Gt"
      | List t,List u -> apply (par("fix walk (xs : list "^par(render_type t)^") (ys : list "^par(render_type u)^") {struct xs} : comparison := match xs, ys with [] , [] => Eq | [], _ => Lt | _, [] => Gt | a :: ax, b :: bx => "^sequence[cross t "a" u "b"] "(walk ax bx)" ^ " end")) [a;c]
      | Option t,Option u -> "match "^a^", "^c^" with None,None=>Eq | None,_=>Lt | _,None=>Gt | Some a,Some b=>"^cross t "a" u "b"^" end"
      | Product ts,Product us ->
          let xs=List.mapi(fun i _->"l"^string_of_int i)ts and ys=List.mapi(fun i _->"r"^string_of_int i)us in
          let rec fields ts xs us ys=match ts,xs,us,ys with
            |t::ts,x::xs,u::us,y::ys->cross t x u y::fields ts xs us ys |_->[] in
          "match "^a^", "^c^" with "^tuple_pattern xs^", "^tuple_pattern ys^" => "^sequence(fields ts xs us ys)(if List.length ts=List.length us then "Eq" else if List.length ts<List.length us then "Lt" else "Gt")^" end"
      | _ when source_tag t >= 0 && source_tag t <> source_tag u -> if source_tag t < source_tag u then "Lt" else "Gt"
      | Named _,Named _ -> let name=request_cross t u in let ps=cross_parameters t u in apply name ((ps @ List.map(fun p->"ops_"^p)ps) @ [a;c])
      | _ -> Data.fail no_region "VariantT" ("source mixfix comparison requires comparison across distinct argument types: " ^ render_type t ^ " / " ^ render_type u)
  in
  let mixed_comparison da ca xs db cb ys =
    match mixop_of_constructor da ca,mixop_of_constructor db cb with
    | Some ma,Some mb ->
        let ma=Domain.Mixfix.fill ma (List.combine ca.fields xs) and mb=Domain.Mixfix.fill mb (List.combine cb.fields ys) in
        let open Domain.Mixfix in
        let tag=function Arg _->0|Atom _->1|Brack _->2|Infix _->3|Seq _->4 in
        let atom a b=Known(Domain.Atom.compare a.it b.it) in
        let rec cmp a b = match a,b with
          | Arg(t,a),Arg(u,b)->(match cross t a u b with "Lt"->Known(-1)|"Gt"->Known 1|"Eq"->Known 0|term->Compare_then(term,Known 0))
          | Atom a,Atom b->atom a b
          | Brack(a,m,b),Brack(c,n,d)->followed_by_lazy(atom a c)(fun () -> followed_by_lazy(cmp m n)(fun () -> atom b d))
          | Infix(a,m,b),Infix(c,n,d)->followed_by_lazy(cmp a c)(fun () -> followed_by_lazy(atom m n)(fun () -> cmp b d))
          | Seq xs,Seq ys->cmps xs ys
          | _->Known(Int.compare(tag a)(tag b))
        and cmps xs ys=match xs,ys with [],[]->Known 0|[],_->Known(-1)|_,[]->Known 1|x::xs,y::ys->followed_by_lazy(cmp x y)(fun () -> cmps xs ys) in
        cmp ma mb
    | _ -> Known 0
  in
  let rank_cache=Hashtbl.create 1000 in
  let ranks d = match Hashtbl.find_opt rank_cache (Data.declaration_name d) with Some ranks->ranks|None->
    let cs=constructors d in
    let sorted=List.sort(fun a b-> match mixop_of_constructor d a,mixop_of_constructor d b with
      |Some a,Some b->Domain.Mixfix.compare ~compare_arg:(fun () ()->0) a b|_->0)cs in
    let ranks=List.mapi(fun i c->c.constructor_name,i)sorted in Hashtbl.add rank_cache (Data.declaration_name d) ranks;ranks in
  let nested_stack=ref [] and nested_counter=ref 0 in
  nested_support := (fun op typ args ->
    match List.find_opt(fun(o,t,_)->o=op && t=typ) !nested_stack with
    |Some(_,_,fn)->apply fn args
    |None->
      let fn="nested_"^string_of_int !nested_counter in incr nested_counter;
      nested_stack:=(op,typ,fn)::!nested_stack;
      let n,ts=match typ with Named(n,ts)->n,ts|_->assert false in
      let d=find n in let ps=Data.declaration_parameters d in
      let cs=List.map(fun c->{c with fields=List.map(replace(List.combine ps ts))c.fields})(constructors d) in
      let body="match x with "^String.concat " " (List.map(fun c->let px,xs=pattern c (fn^"a") in
        "| "^px^" => "^(match op with
        |`Print->printer d c xs |`Unparse->unparser d c xs
        |`Eq|`Cmp->let py,ys=pattern c (fn^"b") in
          let comparisons=List.map2(fun t(x,y)->support op t [x;y])c.fields(List.combine xs ys) in
          let same=if op=`Eq then conjunction comparisons else sequence comparisons "Eq" in
          let others=if List.length cs<2 then "" else if op=`Eq then " | _ => false" else
            let rs=ranks d in
            let exceptional=List.filter_map(fun other->if c.constructor_name=other.constructor_name then None else
              let py,ys=pattern other(fn^"b") in match mixed_comparison d c xs d other ys with Known _->None|code->Some(" | "^py^" => "^comparison_term code))cs in
            String.concat "" exceptional ^ (if List.length exceptional+1=List.length cs then "" else " | _ => Nat.compare "^string_of_int(List.assoc c.constructor_name rs)^" "^apply(n^"_rank")(List.map render_type ts@["y"])) in
          "match y with | "^py^" => "^same^others^" end"))cs)^" end" in
      nested_stack:=List.tl !nested_stack;
      let ty=render_type typ in
      let signature=match op with `Print->"(level : nat) (x : "^ty^")"|`Unparse->"(x : "^ty^")"|_->"(x y : "^ty^")" in
      let result=match op with `Eq->"bool"|`Cmp->"comparison"|`Print->"string"|`Unparse->"option string" in
      apply(par("fix "^fn^" "^signature^" {struct x} : "^result^" := "^body))args);
  let cross_body t u =
    match t,u with
    |Named(n,ts),Named(k,us)->
      let d=find n and e=find k in
      let cs=constructors d and ds=constructors e in
      let instantiate declaration arguments c =
        {c with fields=List.map(replace(List.combine(Data.declaration_parameters declaration)arguments))c.fields} in
      if List.for_all(fun c->Option.is_some(mixop_of_constructor d c))cs && List.for_all(fun c->Option.is_some(mixop_of_constructor e c))ds then (
        let shaped=List.map(fun c->c,Option.get(mixop_of_constructor d c))cs @ List.map(fun c->c,Option.get(mixop_of_constructor e c))ds in
        let shaped=List.sort(fun(_,a)(_,b)->Domain.Mixfix.compare ~compare_arg:(fun () ()->0)a b)shaped in
        let _,_,ranks=List.fold_left(fun(index,previous,acc)(c,mixop)->
          let key=Data.mixop_key mixop in let index=if previous=Some key then index else index+1 in index,Some key,(c.constructor_name,index)::acc)(-1,None,[])shaped in
        "let right_rank := match y with "^String.concat " " (List.map(fun c->let p,_=pattern c "_" in "| "^p^" => "^string_of_int(List.assoc c.constructor_name ranks))ds)^" end in match x with "^
        String.concat " " (List.map(fun ca->let ca=instantiate d ts ca in let px,xs=pattern ca "l" in
          let exceptional=List.filter_map(fun cb->let cb=instantiate e us cb in let py,ys=pattern cb "r" in
            match mixed_comparison d ca xs e cb ys with Known _->None|code->Some("| "^py^" => "^comparison_term code))ds in
          let fallback="Nat.compare "^string_of_int(List.assoc ca.constructor_name ranks)^" right_rank" in
          "| "^px^" => "^(if exceptional=[] then fallback else "match y with "^String.concat " " exceptional^(if List.length exceptional=List.length ds then "" else " | _ => "^fallback)^" end"))cs)^" end")
      else "match x with " ^ String.concat " " (List.map(fun ca->
        let ca=instantiate d ts ca in let px,xs=pattern ca "l" in
        "| "^px^" => match y with " ^ String.concat " " (List.map(fun cb->
          let cb=instantiate e us cb in let py,ys=pattern cb "r" in
          let result=match d,e with
            | Record _,Record _ ->
              let fs=Data.fields ctx (source ctx n).source_name and gs=Data.fields ctx(source ctx k).source_name in
              let rec fields fs ts xs gs us ys=match fs,ts,xs,gs,us,ys with
                |(a,_)::fs,t::ts,x::xs,(b,_)::gs,u::us,y::ys ->
                    let ac=Domain.Atom.compare a.it b.it in
                    if ac<>0 then Known ac else followed_by(Compare_then(cross t x u y,Known 0))(fields fs ts xs gs us ys)
                |[],_,_,[],_,_->Known 0 |[],_,_,_,_,_->Known(-1)|_->Known 1 in
              fields fs ca.fields xs gs cb.fields ys
            | _ -> mixed_comparison d ca xs e cb ys in
          "| "^py^" => "^comparison_term result)ds)^" end")cs)^" end"
    |_->assert false in
  let emit_function_components definitions =
    let indexed=List.map(fun body->let at=String.index body ' ' in String.sub body 0 at,body)definitions in
    let table=Hashtbl.create 1000 in List.iter(fun(n,b)->Hashtbl.add table n b)indexed;
    let dependencies body =
      let hits=Hashtbl.create 100 and word=Buffer.create 80 in
      let flush ()=if Buffer.length word>0 then (let w=Buffer.contents word in if Hashtbl.mem table w then Hashtbl.replace hits w ();Buffer.clear word) in
      let rec scan quoted i=if i>=String.length body then flush () else
        let c=body.[i] in if quoted then
          if c='"' then (if i+1<String.length body && body.[i+1]='"' then scan true(i+2) else scan false(i+1)) else scan true(i+1)
        else if c='"' then (flush();scan true(i+1)) else
          match c with 'a'..'z'|'A'..'Z'|'0'..'9'|'_'->Buffer.add_char word c;scan false(i+1)|_->flush();scan false(i+1)
      in scan false(String.index body ' ');Hashtbl.to_seq_keys hits|>List.of_seq|>List.sort String.compare in
    let next=ref 0 and stack=ref [] in let indices=Hashtbl.create 1000 and low=Hashtbl.create 1000 and active=Hashtbl.create 1000 in
    let rec visit name =
      let i= !next in incr next;Hashtbl.add indices name i;Hashtbl.add low name i;Hashtbl.replace active name true;stack:=name::!stack;
      List.iter(fun dep->if not(Hashtbl.mem indices dep)then(visit dep;Hashtbl.replace low name(min(Hashtbl.find low name)(Hashtbl.find low dep)))
        else if Option.value ~default:false(Hashtbl.find_opt active dep)then Hashtbl.replace low name(min(Hashtbl.find low name)(Hashtbl.find indices dep)))(dependencies(Hashtbl.find table name));
      if Hashtbl.find low name=i then (
        let rec pop acc=match !stack with []->assert false|n::ns->stack:=ns;Hashtbl.replace active n false;let acc=n::acc in if n=name then acc else pop acc in
        let component=pop [] in List.iteri(fun i n->line((if i=0 then "Fixpoint " else "with ")^Hashtbl.find table n))component;line ".")
    in List.iter(fun(n,_)->if not(Hashtbl.mem indices n)then visit n)indexed
  in
  let emitted_cross=Hashtbl.create 100 in
  List.iter (fun m ->
    let names=List.map Data.declaration_name m.declarations in
    active_names := names;
    let rec inline t = match t with
      | Named(n,_) when List.mem n names -> let e=expand [] t in if e=t then t else inline e
      | List t->List(inline t)|Option t->Option(inline t)|Product ts->Product(List.map inline ts)|Named(n,ts)->Named(n,List.map inline ts)|t->t in
    let concrete=List.filter(function Alias _->false|_->true)m.declarations in
    let aliases=List.filter(function Alias _->true|_->false)m.declarations in
    List.iteri(fun i d -> let n=Data.declaration_name d and ps=Data.declaration_parameters d in
      line ((if i=0 then "Inductive " else "with ")^n^" "^params ps^" : Set :=");
      List.iter(fun c -> line("| "^c.constructor_name^" : " ^ String.concat " -> " (List.map (fun t->render_type(inline t))c.fields @ [instantiated n ps]))) (constructors d))concrete;
    if concrete<>[] then line ".";
    List.iter(fun d -> let ps=Data.declaration_parameters d in if ps<>[] then List.iter(fun c->line("Arguments "^c.constructor_name^" {"^String.concat " " ps^"}."))(constructors d))concrete;
    List.iter(function Alias(n,ps,t)->line("Definition "^n^" "^params ps^" := "^render_type(inline t)^".")|_->())aliases;
    List.iter(function Record(n,ps,fs)->List.iteri(fun i (f:binding)->let c=List.hd(constructors(Record(n,ps,fs))) in let p,vs=pattern c "v" in
      line("Definition "^f.name^" "^params ps^" (x : "^instantiated n ps^") : "^render_type(inline f.typ)^" := match x with "^p^" => "^List.nth vs i^" end."))fs|_->())concrete;
    )modules;
  List.iter (fun m ->
    let names=List.map Data.declaration_name m.declarations in
    active_names := names;
    let rec inline t=match t with
      |Named(n,_) when List.mem n names -> let e=expand [] t in if e=t then t else inline e
      |List t->List(inline t)|Option t->Option(inline t)|Product ts->Product(List.map inline ts)|Named(n,ts)->Named(n,List.map inline ts)|t->t in
    let concrete=List.filter(function Alias _->false|_->true)m.declarations in
    let aliases=List.filter(function Alias _->true|_->false)m.declarations in
    List.iter(fun d->if List.length(constructors d)>1 then (
      let n=Data.declaration_name d and ps=Data.declaration_parameters d in let rs=ranks d in
      line("Definition "^n^"_rank "^params ps^" (x : "^instantiated n ps^") : nat := match x with "^
        String.concat " " (List.map(fun c->let p,_=pattern c "_" in "| "^p^" => "^string_of_int(List.assoc c.constructor_name rs))(constructors d))^" end.")))concrete;
    List.iter(fun d->if List.length(constructors d)>1 then (
      let n=Data.declaration_name d and ps=Data.declaration_parameters d in
      List.iter(fun c->let p,vs=pattern c "field" in
        line("Definition "^c.constructor_name^"_payload "^params ps^" (x : "^instantiated n ps^") : option "^par(render_type(Product(List.map inline c.fields)))^" := match x with | "^p^" => Some "^tuple_pattern vs^" | _ => None end.")) (constructors d)))concrete;
    List.iter(fun op ->
      let bodies=List.map(fun d ->
        let body_buffer=Buffer.create 2000 in let line text=Buffer.add_string body_buffer (text^"\n") in
        let n=Data.declaration_name d and ps=Data.declaration_parameters d in
        let fn=(match op with `Eq->equal_name|`Cmp->compare_name|`Print->print_name|`Unparse->unparse_name)n in
        let ty=instantiated n ps in
        line(fn^" "^params ps^" "^capabilities ps^ (if op=`Print then " (level : nat) (x : "^ty^")" else if op=`Unparse then " (x : "^ty^")" else " (x y : "^ty^")")^" {struct x} : "^(match op with `Eq->"bool"|`Cmp->"comparison"|`Print->"string"|`Unparse->"option string")^" :=");
        line "match x with";
        List.iter(fun c -> let p,xs=pattern c "a" in
          line("| "^p^" => " ^ (if op=`Print then printer d c xs else if op=`Unparse then unparser d c xs else
            let q,ys=pattern c "b" in let cs=List.map2(fun t (x,y)->support op (inline t) [x;y])c.fields(List.combine xs ys) in
            let same=if op=`Eq then conjunction cs else sequence cs "Eq" in
            if List.length(constructors d)=1 then "match y with | "^q^" => "^same^" end" else
              let otherwise=if op=`Eq then "false" else
                let ranks=ranks d in
                let fallback="Nat.compare "^string_of_int(List.assoc c.constructor_name ranks)^" "^apply(n^"_rank")(ps@["y"]) in
                let exceptional=List.filter_map(fun other ->
                  if other.constructor_name=c.constructor_name then None else
                  let py,ys=pattern other "b" in
                  match mixed_comparison d c xs d other ys with
                  | Known _ -> None | code -> Some(" | "^py^" => "^comparison_term code)) (constructors d) in
                if exceptional=[] then fallback else "match y with "^String.concat "" exceptional^" | _ => "^fallback^" end" in
              "match "^apply(c.constructor_name^"_payload")(ps@["y"])^" with | Some "^tuple_pattern ys^" => "^same^" | None => "^otherwise^" end"))) (constructors d);
        line "end";Buffer.contents body_buffer) concrete in
      let helpers=ref [] in
      if op=`Cmp then (
        let rec collect () =
          match List.find_opt(fun(_,_,n)->not(Hashtbl.mem emitted_cross n) && not(List.exists(fun(_,_,n0,_)->n=n0) !helpers)) !cross_requests with
          |None->()
          |Some(t,u,name)->let body=cross_body t u in helpers:= !helpers@[t,u,name,body];collect () in
        collect ());
      let helper_bodies=List.map(fun(t,u,name,body)->let ps=cross_parameters t u in
        Hashtbl.add emitted_cross name true;name^" "^params ps^" "^capabilities ps^" (x : "^render_type t^") (y : "^render_type u^") {struct x} : comparison := "^body) !helpers in
      emit_function_components (bodies@helper_bodies)) [`Eq;`Cmp;`Print;`Unparse];
    List.iter(fun d -> let n=Data.declaration_name d and ps=Data.declaration_parameters d in
      let args=(ps @ List.map(fun p->"ops_"^p)ps) in
      line("Definition "^ops_name n^" "^params ps^" "^capabilities ps^" : ValueOps@{Set} "^par(instantiated n ps)^" := {| equal_value := "^apply(equal_name n)args^"; compare_value := "^apply(compare_name n)args^"; print_value := "^apply(print_name n)args^"; unparse_value := "^apply(unparse_name n)args^" |}."))concrete;
    List.iter(function Alias(n,ps,t)-> let t=inline t in
      line("Definition "^ops_name n^" "^params ps^" "^capabilities ps^" : ValueOps@{Set} "^par(instantiated n ps)^" := "^ops_expr t^".");
      List.iter(fun(op,suffix)->line("Definition "^n^suffix^" "^params ps^" "^capabilities ps^" := "^apply op [apply (ops_name n) (ps @ List.map(fun p->"ops_"^p)ps)]^"."))["equal_value","_equal";"compare_value","_compare";"print_value","_print";"unparse_value","_unparse"]|_->())aliases;
    line "")modules;
  Buffer.contents b
