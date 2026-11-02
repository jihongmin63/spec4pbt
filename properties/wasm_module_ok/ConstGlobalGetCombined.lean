import properties.wasm_module_ok.ConstGlobalGetDispatch
import properties.wasm_module_ok.ConstSyntaxDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstGlobalGetCombined

theorem global_get_constant_instruction_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.globalidx) (iit : SpecTec.inferinstrtype)
    (n fin : Nat) :
    ConstSyntaxDecision.syntaxAllowed c (.«GLOBAL.GET» x) = true ∧
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«GLOBAL.GET» x)⟩)
      n (.success (.of iit)) fin ↔
    ∃ t : SpecTec.valtype,
      c.GLOBALS[x]? = some (.GlobalT .Cons t) ∧
      iit =
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses, [t]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) ∧
      fin = n := by
  constructor
  · rintro ⟨hsyntax, hcall⟩
    have hsyntax' :=
      (ConstSyntaxDecision.syntaxAllowed_iff c (.«GLOBAL.GET» x)).1 hsyntax
    have himmutable : ∃ t : SpecTec.valtype,
        c.GLOBALS[x]? = some (.GlobalT .Cons t) := by
      cases hsyntax' with
      | arithmetic _ hm =>
          simp [ConstArithmeticValidation.arithmeticOps] at hm
      | globalGet _ t hget => exact ⟨t, hget⟩
    obtain ⟨t, hget⟩ := himmutable
    obtain ⟨m, t', hget', hiit, hfin⟩ :=
      (ConstGlobalGetDispatch.global_get_dispatch_iff
        c irt x iit n fin).1 hcall
    rw [hget] at hget'
    cases hget'
    exact ⟨t, hget, hiit, hfin⟩
  · rintro ⟨t, hget, hiit, hfin⟩
    constructor
    · exact (ConstSyntaxDecision.syntaxAllowed_iff c (.«GLOBAL.GET» x)).2
        (.globalGet x t hget)
    · exact (ConstGlobalGetDispatch.global_get_dispatch_iff
        c irt x iit n fin).2 ⟨.Cons, t, hget, hiit, hfin⟩

end properties.wasm_module_ok.ConstGlobalGetCombined
