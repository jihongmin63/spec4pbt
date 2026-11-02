import properties.wasm_module_ok.ConstI31Dispatch
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstI31Candidate

theorem i31_effect_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (iit : SpecTec.inferinstrtype) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt .«REF.I31»⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨heffect, _⟩ :=
    ConstI31Dispatch.i31_instruction_effect c irt iit start fin h
  have hmember := FiniteValidTypes.valid_mem_candidateUniverse
    c (.RefT (.«% %» .NoNull .I31HT)) (by rfl)
  refine ⟨[.NumT .I32T], [.RefT (.«% %» .NoNull .I31HT)],
    ?_, ?_, ?_⟩
  · rw [heffect]
  · rw [heffect]
  · simpa using hmember

end properties.wasm_module_ok.ConstI31Candidate
