import properties.wasm_module_ok.ConstFinalPopMatch

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstSingletonMatch

theorem singleton_match_valtype
    (c : SpecTec.context) (u t : SpecTec.valtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Match_resulttype c [u] [t]⟩)
      start (.success (.of ())) fin) :
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_valtype» c.TYPES u t⟩)
        start (.success (.of true)) middle := by
  have hiter :=
    (MatchResulttypeValidation.match_resulttype_success_iff
      c [u] [t] start fin).1 h |>.2
  obtain ⟨middle, hmatch, _⟩ :=
    (MatchResulttypeValidation.match_iter_cons_success_iff
      c u t [] [] start fin).1 hiter
  exact ⟨middle, hmatch⟩

end properties.wasm_module_ok.ConstSingletonMatch
