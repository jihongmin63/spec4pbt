import properties.wasm_module_ok.ConstructiveBodyReferenceBranches
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceBranchMembers
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyNonemptyLabels ConstructiveBodyReferenceBranches ConstructiveBodyProductionCoverage

private theorem peek_mem (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap))
    (p : ConstructiveBodyProductions.Production c stack)
    (hm : p∈((ConstructiveBodyLookup.entries c.LABELS).map fun e => onNull c stack env hs e nu heap hp) ++
      ((ConstructiveBodyNonemptyLabels.all c).flatMap fun label =>
        if hh : CandidateValMatch.candidateValMatch c (.RefT (.«% %» .NoNull heap)) label.last=true then
          [onNonNull c stack env hs label nu heap hp hh] else [])) : p∈all c stack env hs := by
  apply List.mem_append_left
  unfold peeked
  split
  next he => rw [hp] at he; cases he
  next nu' heap' he =>
    have hh : nu'=nu ∧ heap'=heap := by simpa using he.symm.trans hp
    rcases hh with ⟨rfl,rfl⟩
    exact hm

theorem onNull_mem (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (e : ConstructiveBodyLookup.Entry c.LABELS) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) :
    onNull c stack env hs e nu heap hp∈all c stack env hs := by
  apply peek_mem c stack env hs nu heap hp
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨e,ConstructiveBodyLookup.complete _ e,rfl⟩

theorem onNonNull_mem (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (label : Label c) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap))
    (hm : CandidateValMatch.candidateValMatch c (.RefT (.«% %» .NoNull heap)) label.last=true) :
    onNonNull c stack env hs label nu heap hp hm∈all c stack env hs := by
  apply peek_mem c stack env hs nu heap hp
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨label,ConstructiveBodyNonemptyLabels.complete c label,?_⟩
  simp only [hm,dite_true]
  exact List.mem_singleton_self _

theorem onCast_mem (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (label : Label c) (r1 r2 : ConstructiveBodyValidReferences.Ref c)
    (hr : ConstructiveBodyReferenceMatcher.refMatch c r2.value r1.value=true)
    (hm : CandidateValMatch.candidateValMatch c (.RefT r2.value) label.last=true) :
    onCast c stack env label r1 r2 hr hm∈all c stack env hs := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨label,ConstructiveBodyNonemptyLabels.complete c label,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨r1,ConstructiveBodyValidReferences.complete c r1,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨r2,ConstructiveBodyValidReferences.complete c r2,?_⟩
  simp only [hr,dite_true]
  apply List.mem_append_left
  simp only [hm,dite_true]
  exact List.mem_singleton_self _

theorem onCastFail_mem (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (label : Label c) (r1 r2 : ConstructiveBodyValidReferences.Ref c)
    (hr : ConstructiveBodyReferenceMatcher.refMatch c r2.value r1.value=true)
    (hm : CandidateValMatch.candidateValMatch c (.RefT (ConstructiveBodyReferenceDifference.difference r1.value r2.value)) label.last=true) :
    onCastFail c stack env label r1 r2 hr hm∈all c stack env hs := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨label,ConstructiveBodyNonemptyLabels.complete c label,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨r1,ConstructiveBodyValidReferences.complete c r1,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨r2,ConstructiveBodyValidReferences.complete c r2,?_⟩
  simp only [hr,dite_true]
  apply List.mem_append_right
  simp only [hm,dite_true]
  exact List.mem_singleton_self _

theorem onNull_produces (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) (e : ConstructiveBodyLookup.Entry c.LABELS) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) :
    Produces (onNull c stack env hs e nu heap hp) (.BR_ON_NULL e.index) := by
  unfold Produces onNull ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem onNonNull_produces (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) (label : Label c) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap))
    (hm : CandidateValMatch.candidateValMatch c (.RefT (.«% %» .NoNull heap)) label.last=true) :
    Produces (onNonNull c stack env hs label nu heap hp hm) (.BR_ON_NON_NULL label.entry.index) := by
  unfold Produces onNonNull ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem onCast_produces (c : context) (stack : inferresulttype) (env : Env c) (label : Label c) (r1 r2 : ConstructiveBodyValidReferences.Ref c)
    (hr : ConstructiveBodyReferenceMatcher.refMatch c r2.value r1.value=true)
    (hm : CandidateValMatch.candidateValMatch c (.RefT r2.value) label.last=true) :
    Produces (onCast c stack env label r1 r2 hr hm) (.BR_ON_CAST label.entry.index r1.value r2.value) := by
  unfold Produces onCast ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem onCastFail_produces (c : context) (stack : inferresulttype) (env : Env c) (label : Label c) (r1 r2 : ConstructiveBodyValidReferences.Ref c)
    (hr : ConstructiveBodyReferenceMatcher.refMatch c r2.value r1.value=true)
    (hm : CandidateValMatch.candidateValMatch c (.RefT (ConstructiveBodyReferenceDifference.difference r1.value r2.value)) label.last=true) :
    Produces (onCastFail c stack env label r1 r2 hr hm) (.BR_ON_CAST_FAIL label.entry.index r1.value r2.value) := by
  unfold Produces onCastFail ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

#print axioms onCastFail_mem
end properties.wasm_module_ok.ConstructiveBodyReferenceBranchMembers
