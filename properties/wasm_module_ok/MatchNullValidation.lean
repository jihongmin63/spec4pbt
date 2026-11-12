import properties.wasm_module_ok.MatchPrimitiveValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchNullValidation

def matchNullResult (a b : SpecTec.null) : Bool :=
  decide (a = b) || (a == .NoNull && b == .Null)

theorem match_null_total (a b : SpecTec.null) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_null» a b⟩)
      n (.success (.of (matchNullResult a b))) n := by
  cases a <;> cases b
  · simp only [matchNullResult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_null_clauses» .NoNull .NoNull))
      n (.success (.of true)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_null:clause:0» .NoNull .NoNull) n .unmatch n
      unfold SpecTec.«$match_null:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
    · apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$match_null:clause:1»
      exact SpecTecExecution.Eval.bind_success
        (SpecTecExecution.Eval.guard_true rfl)
        (SpecTecExecution.Eval.pure true)
  · simp only [matchNullResult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_null_clauses» .NoNull .Null))
      n (.success (.of true)) n
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«$match_null:clause:0»
    exact SpecTecExecution.Eval.bind_success
      (SpecTecExecution.Eval.guard_true rfl)
      (SpecTecExecution.Eval.bind_success
        (SpecTecExecution.Eval.guard_true rfl)
        (SpecTecExecution.Eval.pure true))
  · simp only [matchNullResult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_null_clauses» .Null .NoNull))
      n (.success (.of false)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«$match_null:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by decide))
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$match_null:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by decide))
      · apply SpecTecExecution.tryClauses_cons_success
        exact SpecTecExecution.Eval.pure false
  · simp only [matchNullResult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_null_clauses» .Null .Null))
      n (.success (.of true)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«$match_null:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by decide))
    · apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$match_null:clause:1»
      exact SpecTecExecution.Eval.bind_success
        (SpecTecExecution.Eval.guard_true rfl)
        (SpecTecExecution.Eval.pure true)

theorem match_null_success_iff (a b : SpecTec.null)
    (result : Bool) (n fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_null» a b⟩)
      n (.success (.of result)) fin ↔
    result = matchNullResult a b ∧ fin = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h (match_null_total a b n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact match_null_total a b fin

end properties.wasm_module_ok.MatchNullValidation
