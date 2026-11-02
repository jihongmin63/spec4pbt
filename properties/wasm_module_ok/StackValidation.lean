import properties.wasm_module_ok.bundle.Helpers
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.StackValidation

theorem stack_total (ts : SpecTec.resulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.ellipses × SpecTec.resulttype,
        SpecTec.Call.«$stack» ts⟩)
      n (.success (.of (SpecTec.ellipses.NoEllipses, ts))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.«$stack_clauses» ts))
    n (.success (.of (SpecTec.ellipses.NoEllipses, ts))) n
  apply SpecTecExecution.tryClauses_cons_success
  exact SpecTecExecution.Eval.pure (SpecTec.ellipses.NoEllipses, ts)

theorem stack_success_iff (ts : SpecTec.resulttype)
    (result : SpecTec.ellipses × SpecTec.resulttype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.ellipses × SpecTec.resulttype,
        SpecTec.Call.«$stack» ts⟩)
      n (.success (.of result)) finalSupply ↔
    result = (SpecTec.ellipses.NoEllipses, ts) ∧
    finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h (stack_total ts n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact stack_total ts finalSupply

end properties.wasm_module_ok.StackValidation
