import properties.wasm_module_ok.CandidateTypesGenerator
import properties.wasm_module_ok.Staged

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateTypesStateStage

/-- The next context is calculated from the selected list; no context is
sampled independently. -/
def typesStateGen (c : SpecTec.context) :
    Gen (List SpecTec.type × SpecTec.context) :=
  CandidateTypesGenerator.typesGen c >>= fun ts =>
    pure (ts, (CandidateTypesDecision.typesResult c ts).getD c)

theorem typesState_support_iff
    (c : SpecTec.context) (ts : List SpecTec.type)
    (out : SpecTec.context) :
    Gen.support (typesStateGen c) (ts, out) ↔
      CandidateTypesDecision.typesResult c ts = some out := by
  simp only [typesStateGen, Gen.Support.support_bind,
    Gen.Support.support_pure]
  constructor
  · rintro ⟨chosen, hchosen, hpure⟩
    obtain ⟨result, hresult⟩ :=
      (CandidateTypesGenerator.typesGen_support_iff c chosen).mp hchosen
    simp only [hresult, Option.getD_some] at hpure
    cases hpure
    exact hresult
  · intro hresult
    refine ⟨ts, ?_, ?_⟩
    · exact (CandidateTypesGenerator.typesGen_support_iff c ts).2
        ⟨out, hresult⟩
    · simp [hresult]

def typesStateStage : Staged.Stage SpecTec.context
    (List SpecTec.type × SpecTec.context) where
  entry := ValidatedTypeChain.ValidatedTypes
  nextEntry := fun output => ValidatedTypeChain.ValidatedTypes output.2
  valid := fun c output =>
    CandidateTypesDecision.typesResult c output.1 = some output.2
  generate := typesStateGen
  always := by
    intro c hc
    exact ⟨([], c), rfl, hc⟩
  sound := by
    intro c output hc hsupport
    have hresult :=
      (typesState_support_iff c output.1 output.2).mp hsupport
    have hsuccess :=
      CandidateTypesDecision.types_success_of_result
        c output.2 output.1 0 hc hresult
    exact ⟨hresult,
      ValidatedTypeChain.types_ok_preserves
        c output.2 output.1 0 0 hc hsuccess⟩
  complete := by
    intro c output _ hvalid _
    exact (typesState_support_iff c output.1 output.2).2 hvalid

end properties.wasm_module_ok.CandidateTypesStateStage
