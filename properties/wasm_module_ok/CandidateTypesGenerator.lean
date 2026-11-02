import properties.wasm_module_ok.CandidateTypesChoices

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateTypesGenerator

/-- Generate a type list by selecting passing recursive groups in order and
carrying each group's computed context into the next choice. -/
def typesGen (c : SpecTec.context) : Gen (List SpecTec.type) :=
  Gen.indexed (fun n => IndexedListStage.chooseList
    (CandidateTypesChoices.choices c n))

theorem typesGen_support_iff
    (c : SpecTec.context) (ts : List SpecTec.type) :
    Gen.support (typesGen c) ts ↔
      ∃ result, CandidateTypesDecision.typesResult c ts = some result := by
  rw [typesGen, Gen.Support.support_indexed]
  constructor
  · rintro ⟨_, n, hn⟩
    have hmem :=
      (IndexedListStage.chooseList_support_some
        (CandidateTypesChoices.choices c n) ts).mp hn
    exact CandidateTypesChoices.choices_sound c n ts hmem
  · rintro ⟨result, hresult⟩
    constructor
    · intro ys n k hn
      apply (IndexedListStage.chooseList_support_some
        (CandidateTypesChoices.choices c (n + k)) ys).2
      exact CandidateTypesChoices.choices_mono c n k ys
        ((IndexedListStage.chooseList_support_some
          (CandidateTypesChoices.choices c n) ys).1 hn)
    · obtain ⟨n, hmem⟩ :=
        CandidateTypesChoices.choices_complete c result ts hresult
      exact ⟨n,
        (IndexedListStage.chooseList_support_some
          (CandidateTypesChoices.choices c n) ts).2 hmem⟩

theorem typesGen_exact
    (c : SpecTec.context) (ts : List SpecTec.type) (n : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c) :
    Gen.support (typesGen c) ts ↔
      ∃ result : SpecTec.context,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context,
            SpecTec.Call.Types_ok c ts⟩)
          n (.success (.of result)) n := by
  constructor
  · rintro hs
    obtain ⟨result, hresult⟩ :=
      (typesGen_support_iff c ts).mp hs
    exact ⟨result,
      (CandidateTypesDecision.types_result_iff_success
        c result ts n hc).mp hresult⟩
  · rintro ⟨result, hsuccess⟩
    apply (typesGen_support_iff c ts).2
    exact ⟨result,
      (CandidateTypesDecision.types_result_iff_success
        c result ts n hc).mpr hsuccess⟩

theorem typesGen_nil (c : SpecTec.context) :
    Gen.support (typesGen c) [] :=
  (typesGen_support_iff c []).2 ⟨c, rfl⟩

end properties.wasm_module_ok.CandidateTypesGenerator
