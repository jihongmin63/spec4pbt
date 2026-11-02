import properties.wasm_module_ok.ConstructiveBodyMemoryOriginal
import properties.wasm_module_ok.ConstructiveBodyMemoryMembers
import properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMemoryCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyMemoryChoices ConstructiveBodyMemoryProductions ConstructiveBodyMemoryMembers ConstructiveBodyProductionCoverage

theorem load (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (op : loadop_)
    (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«LOAD» x op)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«LOAD» x op) effect ∧ finish=n := by
  obtain ⟨mem,got,middle,hx,hop⟩ := ConstructiveBodyMemoryOriginal.load c stack x op effect n finish h
  rcases op with ⟨ty,align,offset,pack⟩
  cases pack with
  | none =>
    obtain ⟨addr,lim,hhead,hoff,ha,_,_⟩ := ConstructiveBodyMemoryOperandOriginal.loadop_ok_none c ty align offset got n middle hop
    let hd : Head c := ⟨addr,lim,hhead⟩
    apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (loadNone c stack env hd mem ty) _ effect n finish
      (loadNone_mem c stack env hd mem ty) _ h
    simpa only [hx] using loadNone_produces c stack env hd mem ty align offset ha hoff
  | some packed =>
    rcases packed with ⟨pt,ext⟩
    obtain ⟨addr,lim,hhead,hoff,ha,hp,_,_⟩ := ConstructiveBodyMemoryOperandOriginal.loadop_ok_some c ty align offset pt ext got n middle hop
    let hd : Head c := ⟨addr,lim,hhead⟩
    apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (loadSome c stack env hd mem ty ⟨pt,hp⟩ ext) _ effect n finish
      (loadSome_mem c stack env hd mem ty ⟨pt,hp⟩ ext) _ h
    simpa only [hx] using loadSome_produces c stack env hd mem ty ⟨pt,hp⟩ ext align offset ha hoff

theorem store (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (op : storeop_)
    (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«STORE» x op)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«STORE» x op) effect ∧ finish=n := by
  obtain ⟨mem,got,middle,hx,hop⟩ := ConstructiveBodyMemoryOriginal.store c stack x op effect n finish h
  rcases op with ⟨ty,align,offset,pack⟩
  cases pack with
  | none =>
    obtain ⟨addr,lim,hhead,hoff,ha,_,_⟩ := ConstructiveBodyMemoryOperandOriginal.storeop_ok_none c ty align offset got n middle hop
    let hd : Head c := ⟨addr,lim,hhead⟩
    apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (storeNone c stack env hd mem ty) _ effect n finish
      (storeNone_mem c stack env hd mem ty) _ h
    simpa only [hx] using storeNone_produces c stack env hd mem ty align offset ha hoff
  | some packed =>
    let pt := packed
    obtain ⟨addr,lim,hhead,hoff,ha,hp,_,_⟩ := ConstructiveBodyMemoryOperandOriginal.storeop_ok_some c ty align offset pt got n middle hop
    let hd : Head c := ⟨addr,lim,hhead⟩
    apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (storeSome c stack env hd mem ty ⟨pt,hp⟩) _ effect n finish
      (storeSome_mem c stack env hd mem ty ⟨pt,hp⟩) _ h
    simpa only [hx] using storeSome_produces c stack env hd mem ty ⟨pt,hp⟩ align offset ha hoff

theorem vload (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (op : vloadop_)
    (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.LOAD» x op)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«VEC.LOAD» x op) effect ∧ finish=n := by
  obtain ⟨mem,got,middle,hx,hop⟩ := ConstructiveBodyMemoryOriginal.vload c stack x op effect n finish h
  rcases op with ⟨ty,align,offset,pack⟩
  cases ty
  cases pack with
  | none =>
    obtain ⟨addr,lim,hhead,hoff,ha,_,_⟩ := ConstructiveBodyMemoryOperandOriginal.vloadop_ok_none c .V128T align offset got n middle hop
    let hd : Head c := ⟨addr,lim,hhead⟩
    apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (vloadNone c stack env hd mem) _ effect n finish
      (vloadNone_mem c stack env hd mem) _ h
    simpa only [hx] using vloadNone_produces c stack env hd mem align offset ha hoff
  | some packed =>
    rcases packed with ⟨pt,ext⟩
    obtain ⟨addr,lim,hhead,hoff,ha,hp,_,_⟩ := ConstructiveBodyMemoryOperandOriginal.vloadop_ok_some c .V128T align offset pt ext got n middle hop
    let hd : Head c := ⟨addr,lim,hhead⟩
    apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (vloadSome c stack env hd mem pt ext) _ effect n finish
      (vloadSome_mem c stack env hd mem pt ext) _ h
    simpa only [hx] using vloadSome_produces c stack env hd mem pt ext align offset ha hoff

theorem vstore (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (op : vstoreop_)
    (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.STORE» x op)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«VEC.STORE» x op) effect ∧ finish=n := by
  obtain ⟨mem,got,middle,hx,hop⟩ := ConstructiveBodyMemoryOriginal.vstore c stack x op effect n finish h
  rcases op with ⟨ty,align,offset,pack⟩
  cases ty
  cases pack
  obtain ⟨addr,lim,hhead,hoff,ha,_,_⟩ := ConstructiveBodyMemoryOperandOriginal.vstoreop_ok_void c .V128T align offset got n middle hop
  let hd : Head c := ⟨addr,lim,hhead⟩
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (ConstructiveBodyMemoryProductions.vstore c stack env hd mem) _ effect n finish
    (vstore_mem c stack env hd mem) _ h
  simpa only [hx] using vstore_produces c stack env hd mem align offset ha hoff

theorem laneLoad (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (op : vlaneop_) (index : Int)
    (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.LOAD_LANE» x op index)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«VEC.LOAD_LANE» x op index) effect ∧ finish=n := by
  obtain ⟨mem,got,middle,hx,hop,hl⟩ := ConstructiveBodyMemoryOriginal.laneLoad c stack x op index effect n finish h
  rcases op with ⟨ty,align,offset,pack⟩
  cases ty
  obtain ⟨addr,lim,hhead,hoff,ha,hp,_,_⟩ := ConstructiveBodyMemoryOperandOriginal.vlaneop_ok_pack c .V128T align offset pack got n middle hop
  let hd : Head c := ⟨addr,lim,hhead⟩
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (ConstructiveBodyMemoryProductions.laneLoad c stack env hd mem pack) _ effect n finish
    (laneLoad_mem c stack env hd mem pack) _ h
  simpa only [hx] using laneLoad_produces c stack env hd mem pack align offset ha hoff index (by rw [laneBound_eq]; exact hl)

theorem laneStore (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (op : vlaneop_) (index : Int)
    (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.STORE_LANE» x op index)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«VEC.STORE_LANE» x op index) effect ∧ finish=n := by
  obtain ⟨mem,got,middle,hx,hop,hl⟩ := ConstructiveBodyMemoryOriginal.laneStore c stack x op index effect n finish h
  rcases op with ⟨ty,align,offset,pack⟩
  cases ty
  obtain ⟨addr,lim,hhead,hoff,ha,hp,_,_⟩ := ConstructiveBodyMemoryOperandOriginal.vlaneop_ok_pack c .V128T align offset pack got n middle hop
  let hd : Head c := ⟨addr,lim,hhead⟩
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (ConstructiveBodyMemoryProductions.laneStore c stack env hd mem pack) _ effect n finish
    (laneStore_mem c stack env hd mem pack) _ h
  simpa only [hx] using laneStore_produces c stack env hd mem pack align offset ha hoff index (by rw [laneBound_eq]; exact hl)

#print axioms load
#print axioms laneStore
end properties.wasm_module_ok.ConstructiveBodyMemoryCoverage
