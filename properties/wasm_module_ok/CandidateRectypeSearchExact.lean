import properties.wasm_module_ok.CandidateRectypeDecision
import properties.wasm_module_ok.IndexedListStage

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateRectypeSearchExact

def passes (c : SpecTec.context) : SpecTec.rectype → Bool
  | .RecT sts => CandidateRectypeDecision.rectypePasses c sts

def candidates (c : SpecTec.context) (n : Nat) :
    List SpecTec.rectype :=
  (Enumeration.decodeCandidates (α := SpecTec.rectype) n).filter (passes c)

theorem candidates_mono (c : SpecTec.context)
    (n k : Nat) (rect : SpecTec.rectype)
    (h : rect ∈ candidates c n) :
    rect ∈ candidates c (n + k) := by
  simp only [candidates, List.mem_filter] at h ⊢
  exact ⟨Enumeration.decodeCandidates_mono n k rect h.1, h.2⟩

/-- Each indexed choice is filtered by the complete element check; no
candidate is sampled and later discarded. -/
def rectypeGroupGen (c : SpecTec.context) : Gen SpecTec.rectype :=
  Gen.indexed (fun n => IndexedListStage.chooseList (candidates c n))

theorem rectypeGroupGen_support_iff
    (c : SpecTec.context) (rect : SpecTec.rectype) :
    Gen.support (rectypeGroupGen c) rect ↔ passes c rect = true := by
  rw [rectypeGroupGen, Gen.Support.support_indexed]
  constructor
  · rintro ⟨_, n, hn⟩
    have hmem :=
      (IndexedListStage.chooseList_support_some (candidates c n) rect).mp hn
    exact (List.mem_filter.mp hmem).2
  · intro hpass
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
          ((List.mem_filter).2 ⟨hmem, hpass⟩)⟩

theorem rectypeGroupGen_exact
    (c : SpecTec.context) (sts : List SpecTec.subtype) (n : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c) :
    Gen.support (rectypeGroupGen c) (.RecT sts) ↔
      ∃ result : SpecTec.context,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨SpecTec.context,
            SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
          n (.success (.of result)) n := by
  exact (rectypeGroupGen_support_iff c (.RecT sts)).trans
    (CandidateRectypeDecision.rectypePasses_iff_success c sts n hc)

end properties.wasm_module_ok.CandidateRectypeSearchExact
