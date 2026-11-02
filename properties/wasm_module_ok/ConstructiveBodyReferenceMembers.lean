import properties.wasm_module_ok.ConstructiveBodyReferenceProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceMembers
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyReferenceProductions ConstructiveBodyProductionCoverage

theorem nullRef_mem (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (heap : heaptype) (hh : heap∈FiniteValidTypes.heapCandidates c) : nullRef c stack env heap hh∈all c stack env hs := by
  simp only [all,List.mem_append]
  left; left; left
  exact List.mem_map.mpr ⟨⟨heap,hh⟩,by simp,rfl⟩

theorem funcRef_mem (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (e : ConstructiveBodyLookup.Entry c.FUNCS) (hr : FreeUnionValidation.HasFunc c.REFS e.index) : funcRef c stack env e hr∈all c stack env hs := by
  simp only [all,List.mem_append]
  left; left; right
  apply List.mem_flatMap.mpr
  refine ⟨e,ConstructiveBodyLookup.complete _ e,?_⟩
  simp only [(ConstRefFuncProduction.has_func_bool_iff _ _).2 hr,dite_true]
  exact List.mem_singleton_self _

theorem static_mem (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (p : ConstructiveBodyProductions.Production c stack)
    (hp : p∈[equal c stack env,i31 c stack env,getI31 c stack env .SX,getI31 c stack env .ZX,arrayLength c stack env]) :
    p∈all c stack env hs := by
  simp only [all,List.mem_append]
  exact Or.inl (Or.inr hp)

theorem peek_mem (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap))
    (p : ConstructiveBodyProductions.Production c stack)
    (hm : p∈[isNull c stack env hs nu heap hp,asNonNull c stack env hs nu heap hp,
      externConvert c stack env .Internalize nu heap hp,externConvert c stack env .Externalize nu heap hp]) :
    p∈all c stack env hs := by
  simp only [all,List.mem_append]
  right
  unfold peeked
  split
  next he => rw [hp] at he; cases he
  next nu' heap' he =>
    have hh : nu'=nu ∧ heap'=heap := by simpa using he.symm.trans hp
    rcases hh with ⟨rfl,rfl⟩
    exact hm

theorem nullRef_produces (c : context) (stack : inferresulttype) (env : Env c) (heap : heaptype) (hh : heap∈FiniteValidTypes.heapCandidates c) :
    Produces (nullRef c stack env heap hh) (.«REF.NULL» heap) := by
  unfold Produces nullRef ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem funcRef_produces (c : context) (stack : inferresulttype) (env : Env c) (e : ConstructiveBodyLookup.Entry c.FUNCS) (hr : FreeUnionValidation.HasFunc c.REFS e.index) :
    Produces (funcRef c stack env e hr) (.«REF.FUNC» e.index) := by
  unfold Produces funcRef ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem equal_produces (c : context) (stack : inferresulttype) (env : Env c) :
    Produces (equal c stack env) (.«REF.EQ») := by
  unfold Produces equal ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem i31_produces (c : context) (stack : inferresulttype) (env : Env c) :
    Produces (i31 c stack env) (.«REF.I31») := by
  unfold Produces i31 ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem getI31_produces (c : context) (stack : inferresulttype) (env : Env c) (extension : SpecTec.extension) :
    Produces (getI31 c stack env extension) (.«I31.GET» extension) := by
  unfold Produces getI31 ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem arrayLength_produces (c : context) (stack : inferresulttype) (env : Env c) :
    Produces (arrayLength c stack env) (.«ARRAY.LEN») := by
  unfold Produces arrayLength ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem isNull_produces (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) :
    Produces (isNull c stack env hs nu heap hp) (.«REF.IS_NULL») := by
  unfold Produces isNull ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem asNonNull_produces (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) :
    Produces (asNonNull c stack env hs nu heap hp) (.«REF.AS_NON_NULL») := by
  unfold Produces asNonNull ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem externConvert_produces (c : context) (stack : inferresulttype) (env : Env c) (op : externop_) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) :
    Produces (externConvert c stack env op nu heap hp) (.«EXTERN.CONVERT» op) := by
  unfold Produces externConvert ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

#print axioms peek_mem
end properties.wasm_module_ok.ConstructiveBodyReferenceMembers
