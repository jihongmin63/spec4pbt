import properties.wasm_module_ok.ConstVectorDispatch
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstVectorCandidate

theorem vector_effect_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.vec_) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«VEC.CONST» v)⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨heffect, _⟩ :=
    ConstVectorDispatch.vec_literal_effect c irt v iit start fin h
  have hmember := FiniteValidTypes.valid_mem_candidateUniverse
    c (.VecT .V128T) (by rfl)
  refine ⟨[], [.VecT .V128T], ?_, ?_, ?_⟩
  · rw [heffect]
  · rw [heffect]
  · simpa using hmember

end properties.wasm_module_ok.ConstVectorCandidate
