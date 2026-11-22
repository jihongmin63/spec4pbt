open Util.Source
open Lang
let write path text=let ch=open_out path in output_string ch text;close_out ch
let named s=Il.VarT(s $ no_region,[]) $ no_region
let nat=Il.NumT `NatT $ no_region and int=Il.NumT `IntT $ no_region
let list t=Il.IterT(t,Il.List) $ no_region
let option t=Il.IterT(t,Il.Opt) $ no_region
let tuple ts=Il.TupleT ts $ no_region
let applied s ts=Il.VarT(s $ no_region,ts) $ no_region
let () =
  let profile=Sys.argv.(1) and output=Sys.argv.(2) in
  let inputs=Array.to_list(Array.sub Sys.argv 3 (Array.length Sys.argv-3)) in
  let source=match Pass.parse inputs with Ok x->x|Error _->failwith "parse" in
  let spec=match Pass.algo inputs with Ok x->x|Error _->failwith "algo" in
  let spec,_=Context.restore_empty_syntax source spec in
  let ctx=match Context.build ~profile:{Coq_ir.name=profile} spec with Ok x->x|Error _->failwith "context" in
  let modules=match Data.lower ctx with Ok x->x|Error _->failwith "data" in
  Casts.reset();
  let count=ref 0 and cases=ref [] in
  let register kind source target= incr count;let head=Casts.request ctx ~source ~target in
    cases := `Assoc["kind",`String kind;"source",`String(Al.Print.string_of_typ source);"target",`String(Al.Print.string_of_typ target);"helper",`String head]::!cases in
  if profile="fixture" then (
    List.iter(fun(a,b)->register "fixture" a b)
      [nat,int;int,nat;list int,list nat;option int,option nat;tuple[nat;option int;list int],tuple[int;option nat;list nat];
       named "narrow",named "broad";named "broad",named "narrow";
       named "aliasNarrow",named "aliasBroad";named "narrowTree",named "broadTree";named "broadTree",named "narrowTree";
       applied "tagged" [nat],applied "tagged" [int];applied "invariant" [nat],applied "invariant" [int];
       named "nestedNarrow",named "nestedBroad";named "nestedBroad",named "nestedNarrow";
       named "mutualNarrowA",named "mutualBroadA";named "mutualBroadA",named "mutualNarrowA";
       applied "tagged" [named "T"],applied "tagged" [named "T"]])
  else (
    let module C=Al.Walk.Collect in
    let base=C.make_base ~default:() ~compose:(fun()()->()) in
    let collect_exp c e=(match e.it with
      | Il.UpCastE(t,x)->register "UpCastE" (x.note $ x.at) t
      | Il.DownCastE(t,x)->register "DownCastE" (x.note $ x.at) t
      | Il.SubE(x,t,s)->
          let rec checks source target=function
            | Il.RecurseSC t->register "RecurseSC" source t
            | Il.TupleSC ss->(match source.it,target.it with Il.TupleT ts,Il.TupleT us->List.iter2(fun(t,u)s->checks t u s)(List.combine ts us)ss|_->())
            | Il.IterSC(_,s)->(match source.it,target.it with Il.IterT(t,_),Il.IterT(u,_)->checks t u s|_->())
            | Il.SkipSC|Il.MixopSC _->() in checks (x.note $ x.at) t s
      | _->());C.default_collect_exp c e in
    let c={base with collect_exp} in
    List.iter(fun d->match d.it with
      |Al.RelD(_,_,_,gs,other,_)->
          let matching(sig_,es,ps)=List.iter(C.collect_exp c)(sig_@es);List.iter(C.collect_prem c)ps in
          let path(_,ps,es)=List.iter(C.collect_prem c)ps;List.iter(C.collect_exp c)es in
          List.iter(fun g->let _,m,ps=g.it in matching m;List.iter path ps)gs;
          Option.iter(fun g->let _,m,p=g.it in matching m;path p)other
      |Al.FuncDecD(_,_,_,_,cs,other,_)->let clause c0=let args,e,ps=c0.it in List.iter(C.collect_arg c)args;C.collect_exp c e;List.iter(C.collect_prem c)ps in List.iter clause cs;Option.iter clause other
      |Al.TableDecD(_,_,_,rows,_)->List.iter(fun r->let es,args,e,ps=r.it in List.iter(C.collect_exp c)es;List.iter(C.collect_arg c)args;C.collect_exp c e;List.iter(C.collect_prem c)ps)rows
      |_->())spec);
  write (output^"/Types.v") (Emit_data.render ctx modules);
  write (output^"/Casts.v") ("From Coq Require Import List ZArith.\nFrom ALCoq Require Import Values.\nRequire Import Types.\nImport ListNotations.\n" ^ Casts.render ctx modules);
  let all=List.concat_map(fun m->m.Coq_ir.declarations)modules in
  let rec variant_cases typ=match typ with
    |Coq_ir.Named(n,ts)->(match List.find(fun d->Data.declaration_name d=n)all with
        |Coq_ir.Alias(_,ps,rhs)->variant_cases(Emit_data.replace(List.combine ps ts)rhs)
        |_->(match (Emit_data.source ctx n).definition.it with
            |Al.TypD(_,_,{it=Il.VariantT cs;_},_)->cs|_->[]))|_->[] in
  let hints cs=List.map(fun(t,_,hs)->Data.mixop_key(fst(Domain.Mixfix.split t.it)),
    List.filter_map(fun h->if El.(h.it.hintid.it="print") then Some(El.Print.string_of_exp El.(h.it.hintexp))else None)hs)cs in
  let hint_mismatches=List.concat_map(fun r->
    let source=variant_cases r.Casts.source in
    let target=variant_cases r.Casts.target in
    List.filter_map(fun(key,hs)->match List.assoc_opt key (hints target) with
      |Some ht when hs<>ht->Some(`Assoc["helper",`String r.Casts.name;"mixop",`String key;"source",`List(List.map(fun s->`String s)hs);"target",`List(List.map(fun s->`String s)ht)])|_->None)(hints source)) !Casts.requests in
  write (output^"/casts.json") (Yojson.Safe.pretty_to_string(`Assoc["occurrences",`Int !count;"helpers",`Int(List.length !Casts.requests);"print_hint_mismatches",`List hint_mismatches;"cases",`List(List.rev !cases)]));
  Printf.printf "%s: %d AL occurrences; %d generated helper pairs\n%!" profile !count (List.length !Casts.requests)
