import properties.wasm_module_ok.ConstructiveBodyBulkProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyBulkOriginal
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyIndexedTypes

theorem tableCopy (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«TABLE.COPY» x y)⟩) n (.success (.of effect)) finish) :
    ∃(dest : Table c) (src : Table c),dest.index=x ∧ src.index=y ∧ ConstructiveBodyReferenceMatcher.refMatch c src.rt dest.rt=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.COPY» x y) 35 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:35» c stack (.«TABLE.COPY» x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:35» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb tail =>
    cases hb
    cases hx : c.TABLES[x]? with
    | none => rw [hx] at tail; cases tail
    | some dest =>
      rw [hx] at tail
      cases dest with | TableT a la ra =>
       cases tail with | bind_success hb tail =>
        cases hb
        cases hy : c.TABLES[y]? with
        | none => rw [hy] at tail; cases tail
        | some src =>
          rw [hy] at tail
          cases src with | TableT b lb rb =>
           cases tail with | bind_success hmatch tail =>
            cases tail with | bind_success hg tail =>
             cases hg with | guard_true htrue =>
              have hm := (ConstructiveBodyReferenceMatcher.exact_call c rb ra _ _ _ env.ready
                (env.tables b lb rb (List.mem_iff_getElem?.mpr ⟨y,hy⟩)) (env.tables a la ra (List.mem_iff_getElem?.mpr ⟨x,hx⟩))).1 hmatch
              exact ⟨⟨x,a,la,ra,hx⟩,⟨y,b,lb,rb,hy⟩,rfl,rfl,hm.1.symm.trans htrue⟩

theorem tableInit (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«TABLE.INIT» x y)⟩) n (.success (.of effect)) finish) :
    ∃(dest : Table c) (src : ConstructiveBodyLookup.Entry c.ELEMS),dest.index=x ∧ src.index=y ∧ ConstructiveBodyReferenceMatcher.refMatch c src.value dest.rt=true := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«TABLE.INIT» x y) 36 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:36» c stack (.«TABLE.INIT» x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:36» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb tail =>
    cases hb
    cases hx : c.TABLES[x]? with
    | none => rw [hx] at tail; cases tail
    | some dest =>
      rw [hx] at tail
      cases dest with | TableT a la ra =>
       cases tail with | bind_success hb tail =>
        cases hb
        cases hy : c.ELEMS[y]? with
        | none => rw [hy] at tail; cases tail
        | some src =>
          rw [hy] at tail
          let rb := src
          cases tail with | bind_success hmatch tail =>
           cases tail with | bind_success hg tail =>
            cases hg with | guard_true htrue =>
             have hm := (ConstructiveBodyReferenceMatcher.exact_call c rb ra _ _ _ env.ready
               (env.elems rb (List.mem_iff_getElem?.mpr ⟨y,hy⟩)) (env.tables a la ra (List.mem_iff_getElem?.mpr ⟨x,hx⟩))).1 hmatch
             exact ⟨⟨x,a,la,ra,hx⟩,⟨y,rb,hy⟩,rfl,rfl,hm.1.symm.trans htrue⟩

theorem memoryCopy (c : context) (stack : inferresulttype) (x y : Nat) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«MEMORY.COPY» x y)⟩) n (.success (.of effect)) finish) :
    ∃(dest : Memory c) (src : Memory c),dest.index=x ∧ src.index=y := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«MEMORY.COPY» x y) 47 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:47» c stack (.«MEMORY.COPY» x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:47» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb tail =>
    cases hb
    cases hx : c.MEMS[x]? with
    | none => rw [hx] at tail; cases tail
    | some dest =>
      rw [hx] at tail
      cases dest with | MemoryT a la =>
       cases tail with | bind_success hb tail =>
        cases hb
        cases hy : c.MEMS[y]? with
        | none => rw [hy] at tail; cases tail
        | some src =>
          rw [hy] at tail
          cases src with | MemoryT b lb =>
           exact ⟨⟨x,a,la,hx⟩,⟨y,b,lb,hy⟩,rfl,rfl⟩

theorem memoryInit (c : context) (stack : inferresulttype) (x y : Nat) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«MEMORY.INIT» x y)⟩) n (.success (.of effect)) finish) :
    ∃(dest : Memory c) (src : Fin c.DATAS.length),dest.index=x ∧ src.val=y := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«MEMORY.INIT» x y) 48 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:48» c stack (.«MEMORY.INIT» x y)) n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:48» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hb tail =>
    cases hb
    cases hx : c.MEMS[x]? with
    | none => rw [hx] at tail; cases tail
    | some dest =>
      rw [hx] at tail
      cases dest with | MemoryT a la =>
       cases tail with | bind_success hb tail =>
        cases hb with | guard_true hy =>
         exact ⟨⟨x,a,la,hx⟩,⟨y,hy.2⟩,rfl,rfl⟩

#print axioms tableCopy
#print axioms memoryInit
end properties.wasm_module_ok.ConstructiveBodyBulkOriginal
