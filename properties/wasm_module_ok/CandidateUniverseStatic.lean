import properties.wasm_module_ok.LocalInitStatic
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateUniverseStatic

theorem candidateUniverse_of_init_locals
    (c c₁ : SpecTec.context) (indices : List SpecTec.idx)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c indices⟩)
      start (.success (.of c₁)) fin) :
    FiniteValidTypes.candidateUniverse c₁ =
      FiniteValidTypes.candidateUniverse c := by
  obtain ⟨ht, hf, hg, _⟩ :=
    LocalInitStatic.init_locals_static_fields c c₁ indices start fin h
  have hheap : FiniteValidTypes.heapCandidates c₁ =
      FiniteValidTypes.heapCandidates c := by
    simp only [FiniteValidTypes.heapCandidates, ht]
  have href : FiniteValidTypes.refCandidates c₁ =
      FiniteValidTypes.refCandidates c := by
    simp only [FiniteValidTypes.refCandidates, hheap]
  have hvalid : FiniteValidTypes.validCandidates c₁ =
      FiniteValidTypes.validCandidates c := by
    simp only [FiniteValidTypes.validCandidates, href]
  simp only [FiniteValidTypes.candidateUniverse,
    FiniteValidTypes.candidateTypes, hvalid, ht, hf, hg]

end properties.wasm_module_ok.CandidateUniverseStatic
