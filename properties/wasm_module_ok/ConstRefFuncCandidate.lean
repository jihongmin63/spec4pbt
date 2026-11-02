import properties.wasm_module_ok.ConstRefFuncEffect
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstRefFuncCandidate

theorem ref_func_effect_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«REF.FUNC» x)⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨dt, hget, _, heffect, _⟩ :=
    (ConstRefFuncEffect.ref_func_instruction_iff
      c irt x iit start fin).1 h
  have hmember := FiniteValidTypes.ref_func_output_mem_candidateUniverse
    c x dt hget
  refine ⟨[], [.RefT (.«% %» .NoNull (.DefHT dt))],
    ?_, ?_, ?_⟩
  · rw [heffect]
  · rw [heffect]
  · simpa using hmember

end properties.wasm_module_ok.ConstRefFuncCandidate
