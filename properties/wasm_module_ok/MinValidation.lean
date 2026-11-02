import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.MinValidation

theorem min_total (a b n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Nat, SpecTec.SpecTecCall.«$min_» a b⟩)
      n (.success (.of (min a b))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$min__clauses» a b) ())
    n (.success (.of (min a b))) n
  by_cases hle : a ≤ b
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$min_:clause:0» a b)
      n (.success (.of (min a b))) n
    unfold SpecTec.«$min_:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hle
    · simpa [Nat.min_eq_left hle] using
        (SpecTecExecution.Eval.pure a (n := n))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$min_:clause:0» a b) n .unmatch n
      unfold SpecTec.«$min_:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false hle)
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$min_:clause:1» a b)
        n (.success (.of (min a b))) n
      simpa [SpecTec.«$min_:clause:1»,
        Nat.min_eq_right (Nat.le_of_not_ge hle)] using
        (SpecTecExecution.Eval.pure b (n := n))

theorem min_success_iff (a b result n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Nat, SpecTec.SpecTecCall.«$min_» a b⟩)
      n (.success (.of result)) finalSupply ↔
    result = min a b ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (min_total a b n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact min_total a b finalSupply

end properties.wasm_module_ok.MinValidation
