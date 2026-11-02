import properties.wasm_module_ok.ConstructiveBodyMemoryOperandOriginal
import properties.wasm_module_ok.ConstructiveBodyMemoryProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMemoryOriginal
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyIndexedTypes ConstructiveBodyEvalReduction

theorem load (c : context) (stack : inferresulttype) (x : Nat) (op : loadop_)
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«LOAD» x op)⟩) n (.success (.of effect)) finish) :
    ∃(mem : Memory c) (ty : numtype) (middle : Nat),mem.index=x ∧
      Eval SpecTec.specTecProgram (.call ⟨numtype,SpecTecCall.Loadop_ok c op⟩) n (.success (.of ty)) middle := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«LOAD» x op) 38 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:38» c stack (.«LOAD» x op)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:38» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hx : c.MEMS[x]? with
  | none => rw [hx] at hs; cases hs
  | some mt =>
    cases mt with | MemoryT addr lim =>
      rw [hx] at hs
      cases hs with | bind_success hop tail =>
        rename_i middle ty
        exact ⟨⟨x,addr,lim,hx⟩,ty,middle,rfl,hop⟩

theorem store (c : context) (stack : inferresulttype) (x : Nat) (op : storeop_)
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«STORE» x op)⟩) n (.success (.of effect)) finish) :
    ∃(mem : Memory c) (ty : numtype) (middle : Nat),mem.index=x ∧
      Eval SpecTec.specTecProgram (.call ⟨numtype,SpecTecCall.Storeop_ok c op⟩) n (.success (.of ty)) middle := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«STORE» x op) 39 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:39» c stack (.«STORE» x op)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:39» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hx : c.MEMS[x]? with
  | none => rw [hx] at hs; cases hs
  | some mt =>
    cases mt with | MemoryT addr lim =>
      rw [hx] at hs
      cases hs with | bind_success hop tail =>
        rename_i middle ty
        exact ⟨⟨x,addr,lim,hx⟩,ty,middle,rfl,hop⟩

theorem vload (c : context) (stack : inferresulttype) (x : Nat) (op : vloadop_)
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.LOAD» x op)⟩) n (.success (.of effect)) finish) :
    ∃(mem : Memory c) (ty : vectype) (middle : Nat),mem.index=x ∧
      Eval SpecTec.specTecProgram (.call ⟨vectype,SpecTecCall.Vloadop_ok c op⟩) n (.success (.of ty)) middle := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«VEC.LOAD» x op) 40 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:40» c stack (.«VEC.LOAD» x op)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:40» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hx : c.MEMS[x]? with
  | none => rw [hx] at hs; cases hs
  | some mt =>
    cases mt with | MemoryT addr lim =>
      rw [hx] at hs
      cases hs with | bind_success hop tail =>
        rename_i middle ty
        exact ⟨⟨x,addr,lim,hx⟩,ty,middle,rfl,hop⟩

theorem vstore (c : context) (stack : inferresulttype) (x : Nat) (op : vstoreop_)
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.STORE» x op)⟩) n (.success (.of effect)) finish) :
    ∃(mem : Memory c) (ty : vectype) (middle : Nat),mem.index=x ∧
      Eval SpecTec.specTecProgram (.call ⟨vectype,SpecTecCall.Vstoreop_ok c op⟩) n (.success (.of ty)) middle := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«VEC.STORE» x op) 41 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:41» c stack (.«VEC.STORE» x op)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:41» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hx : c.MEMS[x]? with
  | none => rw [hx] at hs; cases hs
  | some mt =>
    cases mt with | MemoryT addr lim =>
      rw [hx] at hs
      cases hs with | bind_success hop tail =>
        rename_i middle ty
        exact ⟨⟨x,addr,lim,hx⟩,ty,middle,rfl,hop⟩

theorem laneLoad (c : context) (stack : inferresulttype) (x : Nat) (op : vlaneop_) (index : Int)
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.LOAD_LANE» x op index)⟩) n (.success (.of effect)) finish) :
    ∃(mem : Memory c) (ty : vectype) (middle : Nat),mem.index=x ∧
      Eval SpecTec.specTecProgram (.call ⟨vectype,SpecTecCall.Vlaneop_ok c op⟩) n (.success (.of ty)) middle ∧ index<Int.tdiv 16 (ConstructiveBodyScalarSizes.packSize op.PACK) := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«VEC.LOAD_LANE» x op index) 42 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:42» c stack (.«VEC.LOAD_LANE» x op index)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:42» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hx : c.MEMS[x]? with
  | none => rw [hx] at hs; cases hs
  | some mt =>
    cases mt with | MemoryT addr lim =>
      rw [hx] at hs
      cases hs with | bind_success hop tail =>
        rename_i middle ty
        rw [bind_known _ _ _ _ _ _ (ConstructiveBodyMemoryCalls.vec_size ty middle)] at tail
        rw [bind_known _ _ _ _ _ _ (ConstructiveBodyScalarSizes.pack_size op.PACK middle)] at tail
        cases tail with | bind_success hrequire tail =>
          obtain ⟨hl,_⟩ := (bind_guard _ _ _ _ _).1 tail
          exact ⟨⟨x,addr,lim,hx⟩,ty,middle,rfl,hop,hl⟩

theorem laneStore (c : context) (stack : inferresulttype) (x : Nat) (op : vlaneop_) (index : Int)
    (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.STORE_LANE» x op index)⟩) n (.success (.of effect)) finish) :
    ∃(mem : Memory c) (ty : vectype) (middle : Nat),mem.index=x ∧
      Eval SpecTec.specTecProgram (.call ⟨vectype,SpecTecCall.Vlaneop_ok c op⟩) n (.success (.of ty)) middle ∧ index<Int.tdiv 16 (ConstructiveBodyScalarSizes.packSize op.PACK) := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«VEC.STORE_LANE» x op index) 43 (by decide) rfl (by decide) effect n finish).1 h
  change Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:43» c stack (.«VEC.STORE_LANE» x op index)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:43» at hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  obtain ⟨_,hs⟩ := (bind_guard _ _ _ _ _).1 hs
  cases hx : c.MEMS[x]? with
  | none => rw [hx] at hs; cases hs
  | some mt =>
    cases mt with | MemoryT addr lim =>
      rw [hx] at hs
      cases hs with | bind_success hop tail =>
        rename_i middle ty
        rw [bind_known _ _ _ _ _ _ (ConstructiveBodyMemoryCalls.vec_size ty middle)] at tail
        rw [bind_known _ _ _ _ _ _ (ConstructiveBodyScalarSizes.pack_size op.PACK middle)] at tail
        cases tail with | bind_success hrequire tail =>
          obtain ⟨hl,_⟩ := (bind_guard _ _ _ _ _).1 tail
          exact ⟨⟨x,addr,lim,hx⟩,ty,middle,rfl,hop,hl⟩

#print axioms laneStore
end properties.wasm_module_ok.ConstructiveBodyMemoryOriginal
