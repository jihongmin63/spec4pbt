import properties.wasm_module_ok.ConstLiteralDispatch
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstLiteralCandidate

theorem literal_effect_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.num_) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.CONST v)⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨heffect, _⟩ :=
    ConstLiteralDispatch.const_literal_effect c irt v iit start fin h
  have hvalid : ValtypeValidation.valtypeValid c
      (.NumT (ConstLiteralEffect.numericType v)) = true := by
    cases v <;> rfl
  have hmember := FiniteValidTypes.valid_mem_candidateUniverse
    c (.NumT (ConstLiteralEffect.numericType v)) hvalid
  refine ⟨[], [.NumT (ConstLiteralEffect.numericType v)], ?_, ?_, ?_⟩
  · rw [heffect]
  · rw [heffect]
  · simpa using hmember

end properties.wasm_module_ok.ConstLiteralCandidate
