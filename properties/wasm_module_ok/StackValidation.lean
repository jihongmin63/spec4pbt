import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.StackValidation

theorem stack_total (ts : SpecTec.resulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.ellipses × SpecTec.resulttype,
        SpecTec.SpecTecCall.«$stack» ts⟩)
      n (.success (.of (SpecTec.ellipses.NoEllipses, ts))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$stack_clauses» ts) ())
    n (.success (.of (SpecTec.ellipses.NoEllipses, ts))) n
  apply SpecTecExecution.firstSuccess_cons_success
  exact SpecTecExecution.Eval.pure (SpecTec.ellipses.NoEllipses, ts)

theorem stack_success_iff (ts : SpecTec.resulttype)
    (result : SpecTec.ellipses × SpecTec.resulttype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.ellipses × SpecTec.resulttype,
        SpecTec.SpecTecCall.«$stack» ts⟩)
      n (.success (.of result)) finalSupply ↔
    result = (SpecTec.ellipses.NoEllipses, ts) ∧
    finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (stack_total ts n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact stack_total ts finalSupply

end properties.wasm_module_ok.StackValidation
