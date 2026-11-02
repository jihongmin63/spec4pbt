import properties.wasm_module_ok.ConstNumericBinopDispatch
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstBinopCandidate

theorem binop_effect_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.binop_) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.BINOP op)⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨nt, _, heffect⟩ :=
    (ConstNumericBinopDispatch.numeric_binop_dispatch_iff
      c irt op iit start fin).1 h
  have hvalid : ValtypeValidation.valtypeValid c (.NumT nt) = true := by
    cases nt <;> rfl
  have hmember := FiniteValidTypes.valid_mem_candidateUniverse
    c (.NumT nt) hvalid
  refine ⟨[.NumT nt, .NumT nt], [.NumT nt], ?_, ?_, ?_⟩
  · rw [heffect]
  · rw [heffect]
  · simpa using hmember

end properties.wasm_module_ok.ConstBinopCandidate
