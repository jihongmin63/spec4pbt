import properties.wasm_module_ok.MakeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.RevDecision

theorem rev_total (X : Type) (xs : List X) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List X, SpecTec.SpecTecCall.«$rev_» X xs⟩)
      start (.success (.of xs.reverse)) start := by
  induction xs generalizing start with
  | nil =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$rev__clauses» X []) ())
      start (.success (.of ([] : List X))) start
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$rev_:clause:0» X [])
      start (.success (.of ([] : List X))) start
    unfold SpecTec.«$rev_:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · exact SpecTecExecution.Eval.pure []
  | cons x xs ih =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$rev__clauses» X (x :: xs)) ())
      start (.success (.of (x :: xs).reverse)) start
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$rev_:clause:0» X (x :: xs))
        start .unmatch start
      unfold SpecTec.«$rev_:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false (by simp)
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$rev_:clause:1» X (x :: xs))
        start (.success (.of (x :: xs).reverse)) start
      unfold SpecTec.«$rev_:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true (by simp)
      · apply SpecTecExecution.Eval.bind_success (ih start)
        simpa using (SpecTecExecution.Eval.pure (xs.reverse ++ [x]))

theorem rev_success_iff_result
    (X : Type) (xs result : List X) (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List X, SpecTec.SpecTecCall.«$rev_» X xs⟩)
      start (.success (.of result)) fin ↔
    result = xs.reverse ∧ fin = start := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (rev_total X xs start)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact rev_total X xs fin

end properties.wasm_module_ok.RevDecision
