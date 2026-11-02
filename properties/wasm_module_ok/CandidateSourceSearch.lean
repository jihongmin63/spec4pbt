import properties.wasm_module_ok.CandidateSourceChecks
import properties.wasm_module_ok.CandidateRectypeSearch

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateSourceSearch

/-- The candidate context is computed first; the source check uses that same
context after the two finite pre-match readiness checks. -/
def preSourceReady (c : SpecTec.context) : SpecTec.rectype → Bool
  | .RecT sts =>
      CandidateRectypeSearch.preMatchReady c (.RecT sts) &&
        match CandidateRectypeTable.candidateContext c sts with
        | none => false
        | some candidate => CandidateSourceChecks.sourceChecks candidate sts

def candidates (c : SpecTec.context) (n : Nat) :
    List SpecTec.rectype :=
  (Enumeration.decodeCandidates (α := SpecTec.rectype) n).filter
    (preSourceReady c)

theorem candidates_mono (c : SpecTec.context)
    (n k : Nat) (rect : SpecTec.rectype)
    (h : rect ∈ candidates c n) :
    rect ∈ candidates c (n + k) := by
  simp only [candidates, List.mem_filter] at h ⊢
  exact ⟨Enumeration.decodeCandidates_mono n k rect h.1, h.2⟩

def sourceGroupGen (c : SpecTec.context) : Gen SpecTec.rectype :=
  Gen.indexed (fun n => IndexedListStage.chooseList (candidates c n))

theorem sourceGroupGen_support_iff
    (c : SpecTec.context) (rect : SpecTec.rectype) :
    Gen.support (sourceGroupGen c) rect ↔
      preSourceReady c rect = true := by
  rw [sourceGroupGen, Gen.Support.support_indexed]
  constructor
  · rintro ⟨_, n, hn⟩
    have hmem :=
      (IndexedListStage.chooseList_support_some (candidates c n) rect).mp hn
    exact (List.mem_filter.mp hmem).2
  · intro hready
    constructor
    · intro x n k hn
      apply (IndexedListStage.chooseList_support_some
        (candidates c (n + k)) x).2
      exact candidates_mono c n k x
        ((IndexedListStage.chooseList_support_some
          (candidates c n) x).1 hn)
    · obtain ⟨n, hmem⟩ := Enumeration.decodeCandidates_complete rect
      exact ⟨n,
        (IndexedListStage.chooseList_support_some
          (candidates c n) rect).2
          ((List.mem_filter).2 ⟨hmem, hready⟩)⟩

theorem sourceGroupGen_support_of_success
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    Gen.support (sourceGroupGen c) (.RecT sts) := by
  apply (sourceGroupGen_support_iff c (.RecT sts)).2
  have hready := CandidateRectypeSearch.success_preMatchReady
    c result sts start finish hc hrect
  have hcandidate := CandidateRectypeTable.rectype_success_candidateContext
    c result sts start finish hrect
  have hsource := CandidateSourceChecks.rectype_success_sourceChecks
    c result result sts start finish hrect hcandidate
  simp [preSourceReady, hready, hcandidate, hsource]

theorem sourceGroupGen_candidate_checks
    (c : SpecTec.context) (sts : List SpecTec.subtype)
    (h : Gen.support (sourceGroupGen c) (.RecT sts)) :
    ∃ candidate,
      CandidateRectypeTable.candidateContext c sts = some candidate ∧
      CandidateTypeReady.Ready candidate ∧
      CandidateNestedReady.nestedTableReady candidate = true ∧
      CandidateSourceChecks.sourceChecks candidate sts = true := by
  have hpre := (sourceGroupGen_support_iff c (.RecT sts)).mp h
  cases hcandidate : CandidateRectypeTable.candidateContext c sts with
  | none => simp [preSourceReady, hcandidate] at hpre
  | some candidate =>
      have hboth : CandidateRectypeSearch.preMatchReady c (.RecT sts) = true ∧
          CandidateSourceChecks.sourceChecks candidate sts = true := by
        simpa [preSourceReady, hcandidate, Bool.and_eq_true] using hpre
      have hpre' : Gen.support
          (CandidateRectypeSearch.readyGroupGen c) (.RecT sts) :=
        (CandidateRectypeSearch.readyGroupGen_support_iff c (.RecT sts)).2
          hboth.1
      obtain ⟨candidate', hcontext', hready, hnested⟩ :=
        CandidateRectypeSearch.readyGroupGen_candidate_nested_ready
          c sts hpre'
      have heq : candidate' = candidate :=
        Option.some.inj (hcontext'.symm.trans hcandidate)
      subst candidate'
      exact ⟨candidate, rfl, hready, hnested, hboth.2⟩

end properties.wasm_module_ok.CandidateSourceSearch
