import properties.wasm_module_ok.ConstArrayImplicitDispatch
import properties.wasm_module_ok.ConstArrayExplicitDispatch
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArrayNewCandidate

theorem array_new_implicit_effect_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW» x .Implicit)⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨yt, t, dt, middle, finish, _, _, _, hget, heffect⟩ :=
    (ConstArrayImplicitDispatch.array_new_implicit_dispatch_iff
      c irt x iit start fin).1 h
  have hmember :=
    FiniteValidTypes.type_constructor_output_mem_candidateUniverse
      c x dt hget
  refine ⟨[.NumT .I32T],
    [.RefT (.«% %» .NoNull (.DefHT dt))], ?_, ?_, ?_⟩
  · rw [heffect]
  · rw [heffect]
  · simpa using hmember

theorem array_new_explicit_effect_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW» x .Explicit)⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨yt, t, dt, middle, _, _, hget, heffect⟩ :=
    (ConstArrayExplicitDispatch.array_new_explicit_dispatch_iff
      c irt x iit start fin).1 h
  have hmember :=
    FiniteValidTypes.type_constructor_output_mem_candidateUniverse
      c x dt hget
  refine ⟨[t, .NumT .I32T],
    [.RefT (.«% %» .NoNull (.DefHT dt))], ?_, ?_, ?_⟩
  · rw [heffect]
  · rw [heffect]
  · simpa using hmember

end properties.wasm_module_ok.ConstArrayNewCandidate
