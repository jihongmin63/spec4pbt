import properties.wasm_module_ok.ConstArrayFixedDispatch
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArrayFixedCandidate

theorem array_new_fixed_effect_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (count : SpecTec.n)
    (iit : SpecTec.inferinstrtype) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt
          (.«ARRAY.NEW_FIXED» x count)⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨yt, t, dt, middle, _, _, hget, heffect⟩ :=
    (ConstArrayFixedDispatch.array_new_fixed_dispatch_iff
      c irt x count iit start fin).1 h
  have hmember :=
    FiniteValidTypes.type_constructor_output_mem_candidateUniverse
      c x dt hget
  refine ⟨MakeValidation.makeResult t count,
    [.RefT (.«% %» .NoNull (.DefHT dt))], ?_, ?_, ?_⟩
  · rw [heffect]
  · rw [heffect]
  · simpa using hmember

end properties.wasm_module_ok.ConstArrayFixedCandidate
