import properties.wasm_module_ok.ConstGlobalGetDispatch
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstGlobalGetCandidate

theorem global_get_effect_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.globalidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«GLOBAL.GET» x)⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨m, t, hget, heffect, _⟩ :=
    (ConstGlobalGetDispatch.global_get_dispatch_iff
      c irt x iit start fin).1 h
  have hmember := FiniteValidTypes.global_output_mem_candidateUniverse
    c x m t hget
  refine ⟨[], [t], ?_, ?_, ?_⟩
  · rw [heffect]
  · rw [heffect]
  · simpa using hmember

end properties.wasm_module_ok.ConstGlobalGetCandidate
