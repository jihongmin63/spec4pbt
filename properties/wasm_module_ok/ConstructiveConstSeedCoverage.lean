import properties.wasm_module_ok.ConstructiveConstGeneration
set_option autoImplicit false
universe u
namespace properties.wasm_module_ok.ConstructiveConstSeedCoverage
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders properties.wasm_module_ok.ConstructiveConstAggregateBuilders
open properties.wasm_module_ok.ConstructiveConstTableCore properties.wasm_module_ok.ConstructiveConstTableSeeds properties.wasm_module_ok.ConstructiveConstTableExpand
open properties.wasm_module_ok.ConstructiveConstTableCoverage properties.wasm_module_ok.ConstructiveConstLiteralGen

theorem covers_flatMap {c : context} {α : Type u} {xs : List α} {f : α → List (Entry c)}
    {tree : Tree} (x : α) (hx : x∈xs) (h : Covers (f x) tree) : Covers (xs.flatMap f) tree := by
  apply covers_mono (fun e he => List.mem_flatMap.mpr ⟨x,hx,he⟩) h

theorem pure_cover (c : context) (hp : CandidateUniverseReady.Provenance c) (u : valtype)
    (t : Typed c u) : Covers [entry c hp u t (Audited.pure t)] t.val :=
  ⟨entry c hp u t (Audited.pure t),by simp,t,rfl,rfl⟩

theorem number_cover (c : context) (hp : CandidateUniverseReady.Provenance c) (v : num_) :
    Covers (literalEntries c hp) (number c v).val := by
  cases v with
  | I32 a => exact ⟨entry c hp _ (number c (.I32 0)) ⟨numbers c .I32T,numbers_audit c .I32T⟩,
      by simp [literalEntries,ConstLiteralEffect.numericType],number c (.I32 a),numbers_support c (.I32 a),rfl⟩
  | I64 a => exact ⟨entry c hp _ (number c (.I64 0)) ⟨numbers c .I64T,numbers_audit c .I64T⟩,
      by simp [literalEntries,ConstLiteralEffect.numericType],number c (.I64 a),numbers_support c (.I64 a),rfl⟩
  | F32 a => exact ⟨entry c hp _ (number c (.F32 (.POS .INF))) ⟨numbers c .F32T,numbers_audit c .F32T⟩,
      by simp [literalEntries,ConstLiteralEffect.numericType],number c (.F32 a),numbers_support c (.F32 a),rfl⟩
  | F64 a => exact ⟨entry c hp _ (number c (.F64 (.POS .INF))) ⟨numbers c .F64T,numbers_audit c .F64T⟩,
      by simp [literalEntries,ConstLiteralEffect.numericType],number c (.F64 a),numbers_support c (.F64 a),rfl⟩

theorem vector_cover (c : context) (hp : CandidateUniverseReady.Provenance c) (v : vec_) :
    Covers (literalEntries c hp) (vector c v).val :=
  ⟨entry c hp _ (vector c (.V128 0)) ⟨vectors c,vectors_audit c⟩,
    by simp [literalEntries,ConstLiteralEffect.numericType],vector c v,vectors_support c v,rfl⟩

theorem null_cover (c : context) (hp : CandidateUniverseReady.Provenance c)
    (ht : heaptype) (hh : HeaptypeValidation.heaptypeValid c ht=true) :
    Covers (nullEntries c hp) (nullRef c ht hh).val := by
  let x : {ht // ht∈FiniteValidTypes.heapCandidates c} := ⟨ht,(FiniteValidTypes.heapCandidates_spec c ht).2 hh⟩
  exact ⟨entry c hp _ (nullRef c ht hh) (Audited.pure (nullRef c ht hh)),
    List.mem_map.mpr ⟨x,by simp,rfl⟩,nullRef c ht hh,rfl,rfl⟩

theorem function_cover (c : context) (hp : CandidateUniverseReady.Provenance c)
    (x : Nat) (dt : deftype) (hx : c.FUNCS[x]?=some dt) (hr : FreeUnionValidation.HasFunc c.REFS x) :
    Covers (functionEntries c hp) (funcRef c x dt hx hr).val := by
  have hbound : x<c.FUNCS.length := (List.getElem?_eq_some_iff.mp hx).1
  let ix : Fin c.FUNCS.length := ⟨x,(List.getElem?_eq_some_iff.mp hx).1⟩
  have he : c.FUNCS[x]=dt := (List.getElem?_eq_some_iff.mp hx).2
  subst dt
  have hb := (ConstRefFuncProduction.has_func_bool_iff c.REFS x).2 hr
  unfold functionEntries
  apply covers_flatMap ix (by simp)
  simp only [ix,hb,dif_pos]
  exact pure_cover c hp _ (funcRef c x c.FUNCS[x] hx hr)

theorem global_cover (c : context) (hp : CandidateUniverseReady.Provenance c)
    (x : Nat) (u : valtype) (hx : c.GLOBALS[x]?=some (.GlobalT .Cons u)) :
    Covers (globalEntries c hp) (global c x u hx).val := by
  let ix : Fin c.GLOBALS.length := ⟨x,(List.getElem?_eq_some_iff.mp hx).1⟩
  have he : c.GLOBALS[ix.val]=.GlobalT .Cons u := by simpa [ix] using (List.getElem?_eq_some_iff.mp hx).2
  unfold globalEntries
  apply covers_flatMap ix (by simp)
  split
  · rename_i t hgt
    have ht : t=u := by simpa only [he,globaltype.GlobalT.injEq,true_and] using hgt.symm
    subst t
    exact pure_cover c hp _ (global c x u hx)
  · rename_i t hgt
    simp [he] at hgt

private theorem struct_ext {c : context} {a b : StructIndex c}
    (hi : a.index=b.index) (hd : a.definition=b.definition) (hf : a.fields=b.fields) : a=b := by
  cases a; cases b; cases hi; cases hd; cases hf; rfl

private theorem array_ext {c : context} {a b : ArrayIndex c}
    (hi : a.index=b.index) (hd : a.definition=b.definition) (hf : a.field=b.field) : a=b := by
  cases a; cases b; cases hi; cases hd; cases hf; rfl

theorem struct_index_mem (c : context) (i : StructIndex c) : i∈structIndices c := by
  let ix : Fin c.TYPES.length := ⟨i.index,(List.getElem?_eq_some_iff.mp i.lookup).1⟩
  have he : c.TYPES[ix.val]=i.definition := by simpa [ix] using (List.getElem?_eq_some_iff.mp i.lookup).2
  unfold structIndices
  apply List.mem_flatMap.mpr
  refine ⟨ix,by simp,?_⟩
  split
  · rename_i fields hst
    have hf : fields=i.fields := by simpa only [he,i.expansion,Option.some.injEq,strtype.DefStructT.injEq,structtype.StructT.injEq] using hst.symm
    subst fields
    simp only [List.mem_singleton]
    exact struct_ext rfl he.symm rfl
  · rename_i hnot
    exact False.elim (hnot i.fields (by rw [he]; exact i.expansion))

theorem array_index_mem (c : context) (i : ArrayIndex c) : i∈arrayIndices c := by
  let ix : Fin c.TYPES.length := ⟨i.index,(List.getElem?_eq_some_iff.mp i.lookup).1⟩
  have he : c.TYPES[ix.val]=i.definition := by simpa [ix] using (List.getElem?_eq_some_iff.mp i.lookup).2
  unfold arrayIndices
  apply List.mem_flatMap.mpr
  refine ⟨ix,by simp,?_⟩
  split
  · rename_i field hst
    have hf : field=i.field := by simpa only [he,i.expansion,Option.some.injEq,strtype.DefArrayT.injEq,arraytype.ArrayT.injEq] using hst.symm
    subst field
    simp only [List.mem_singleton]
    exact array_ext rfl he.symm rfl
  · rename_i hnot
    exact False.elim (hnot i.field (by rw [he]; exact i.expansion))

theorem implicit_struct_cover (c : context) (hp : CandidateUniverseReady.Provenance c)
    (i : StructIndex c) (hd : StructImplicitFieldsDecision.structFieldsDefaultable i.fields=true) :
    Covers (implicitStructEntries c hp) (structImplicit c i hd).val := by
  unfold implicitStructEntries
  apply covers_flatMap i (struct_index_mem c i)
  simpa only [dif_pos hd] using pure_cover c hp _ (structImplicit c i hd)

theorem empty_array_cover (c : context) (hp : CandidateUniverseReady.Provenance c) (i : ArrayIndex c) :
    Covers (emptyArrayEntries c hp) (arrayFixed c i 0 (emptyOperands c)).val := by
  exact ⟨entry c hp _ (arrayFixed c i 0 (emptyOperands c)) (Audited.pure (arrayFixed c i 0 (emptyOperands c))),
    List.mem_map.mpr ⟨i,array_index_mem c i,rfl⟩,arrayFixed c i 0 (emptyOperands c),rfl,rfl⟩

#print axioms function_cover
#print axioms implicit_struct_cover
end properties.wasm_module_ok.ConstructiveConstSeedCoverage
