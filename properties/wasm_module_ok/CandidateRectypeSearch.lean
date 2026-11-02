import properties.wasm_module_ok.CandidateRectypeTable
import properties.wasm_module_ok.CandidateNestedReady
import properties.wasm_module_ok.IndexedListStage

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateRectypeSearch

/-- A terminating pre-match test on a decoded recursive-group candidate. -/
def preMatchReady (c : SpecTec.context) : SpecTec.rectype → Bool
  | .RecT sts =>
      match CandidateRectypeTable.candidateContext c sts with
      | none => false
      | some candidate =>
          CandidateTypeReadyDecide.tableReady candidate &&
            CandidateNestedReady.nestedTableReady candidate

def candidates (c : SpecTec.context) (n : Nat) :
    List SpecTec.rectype :=
  (Enumeration.decodeCandidates (α := SpecTec.rectype) n).filter
    (preMatchReady c)

theorem candidates_mono (c : SpecTec.context)
    (n k : Nat) (rect : SpecTec.rectype)
    (h : rect ∈ candidates c n) :
    rect ∈ candidates c (n + k) := by
  simp only [candidates, List.mem_filter] at h ⊢
  exact ⟨Enumeration.decodeCandidates_mono n k rect h.1, h.2⟩

/-- The search enumerates only candidates passing the pre-match test.
Further semantic checks belong to the Types stage. -/
def readyGroupGen (c : SpecTec.context) : Gen SpecTec.rectype :=
  Gen.indexed (fun n => IndexedListStage.chooseList (candidates c n))

theorem readyGroupGen_support_iff
    (c : SpecTec.context) (rect : SpecTec.rectype) :
    Gen.support (readyGroupGen c) rect ↔
      preMatchReady c rect = true := by
  rw [readyGroupGen, Gen.Support.support_indexed]
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

theorem readyGroupGen_candidate_ready
    (c : SpecTec.context) (sts : List SpecTec.subtype)
    (h : Gen.support (readyGroupGen c) (.RecT sts)) :
    ∃ candidate,
      CandidateRectypeTable.candidateContext c sts = some candidate ∧
      CandidateTypeReady.Ready candidate := by
  have hpre := (readyGroupGen_support_iff c (.RecT sts)).mp h
  cases hcandidate : CandidateRectypeTable.candidateContext c sts with
  | none =>
      simp [preMatchReady, hcandidate] at hpre
  | some candidate =>
      have hboth : CandidateTypeReadyDecide.tableReady candidate = true ∧
          CandidateNestedReady.nestedTableReady candidate = true := by
        simpa [preMatchReady, hcandidate, Bool.and_eq_true] using hpre
      have htable := hboth.1
      exact ⟨candidate, rfl,
        (CandidateTypeReadyDecide.tableReady_true_iff_ready candidate).mp
          htable⟩

theorem readyGroupGen_candidate_nested_ready
    (c : SpecTec.context) (sts : List SpecTec.subtype)
    (h : Gen.support (readyGroupGen c) (.RecT sts)) :
    ∃ candidate,
      CandidateRectypeTable.candidateContext c sts = some candidate ∧
      CandidateTypeReady.Ready candidate ∧
      CandidateNestedReady.nestedTableReady candidate = true := by
  have hpre := (readyGroupGen_support_iff c (.RecT sts)).mp h
  cases hcandidate : CandidateRectypeTable.candidateContext c sts with
  | none => simp [preMatchReady, hcandidate] at hpre
  | some candidate =>
      have hboth : CandidateTypeReadyDecide.tableReady candidate = true ∧
          CandidateNestedReady.nestedTableReady candidate = true := by
        simpa [preMatchReady, hcandidate, Bool.and_eq_true] using hpre
      exact ⟨candidate, rfl,
        (CandidateTypeReadyDecide.tableReady_true_iff_ready candidate).mp
          hboth.1, hboth.2⟩

theorem success_preMatchReady
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    preMatchReady c (.RecT sts) = true := by
  have hcontext := CandidateRectypeTable.rectype_success_candidateContext
    c result sts start finish hrect
  have hready := CandidateTypeReadySuccess.rectype_success_tableReady
    c result sts start finish hc hrect
  have hnested := CandidateNestedReady.rectype_success_nestedTableReady
    c result sts start finish hc hrect
  simp [preMatchReady, hcontext, hready, hnested]

theorem readyGroupGen_support_of_success
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    Gen.support (readyGroupGen c) (.RecT sts) :=
  (readyGroupGen_support_iff c (.RecT sts)).2
    (success_preMatchReady c result sts start finish hc hrect)

end properties.wasm_module_ok.CandidateRectypeSearch
