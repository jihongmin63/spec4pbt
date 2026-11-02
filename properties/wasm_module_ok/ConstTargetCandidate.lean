import properties.wasm_module_ok.ConstTraceCandidate
import properties.wasm_module_ok.ConstSingletonMatch

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstTargetCandidate

theorem const_ok_target_has_candidate_match
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      start (.success (.of ())) fin) :
    ∃ u : SpecTec.valtype,
      u ∈ FiniteValidTypes.candidateUniverse c ∧
      ∃ before after : Nat,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool,
            SpecTec.SpecTecCall.«$match_valtype» c.TYPES u t⟩)
          before (.success (.of true)) after := by
  obtain ⟨irt, indices, ellipses, middle,
    _, hno, hclosed, hpop⟩ :=
    ConstTraceCandidate.const_ok_trace_candidates
      c t xs start fin h
  rcases irt with ⟨e, stack⟩
  dsimp at hno hclosed hpop
  subst e
  obtain ⟨u, hstack, _⟩ :=
    ConstFinalPopShape.final_const_pop_singleton
      c t stack ellipses middle fin hpop
  subst stack
  have hu : u ∈ FiniteValidTypes.candidateUniverse c :=
    hclosed u (by simp)
  obtain ⟨before, after, hresult⟩ :=
    ConstFinalPopMatch.final_const_pop_matches
      c t u ellipses middle fin hpop
  obtain ⟨matchFin, hmatch⟩ :=
    ConstSingletonMatch.singleton_match_valtype
      c u t before after hresult
  exact ⟨u, hu, before, matchFin, hmatch⟩

end properties.wasm_module_ok.ConstTargetCandidate
