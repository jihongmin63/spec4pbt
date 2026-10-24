import properties.wasm_module_not_ok.MatchPrimitiveValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def matchNull (a b : SpecTec.null) : Bool :=
  match a, b with
  | .Null, .NoNull => false
  | _, _ => true

theorem match_null_no_null_null (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_null» .NoNull .Null⟩)
      start (.success (.of true)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_null_clauses» .NoNull .Null) ())
    start (.success (.of true)) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_null:clause:0» .NoNull .Null)
    start (.success (.of true)) start
  unfold SpecTec.«$match_null:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by decide)
    · exact SpecTecExecution.Eval.pure true

theorem match_null_no_null_no_null (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_null» .NoNull .NoNull⟩)
      start (.success (.of true)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_null_clauses» .NoNull .NoNull) ())
    start (.success (.of true)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_null:clause:0» .NoNull .NoNull)
      start .unmatch start
    unfold SpecTec.«$match_null:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by decide)
    · apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false (by decide)
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_null:clause:1» .NoNull .NoNull)
      start (.success (.of true)) start
    unfold SpecTec.«$match_null:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · exact SpecTecExecution.Eval.pure true

theorem match_null_null_null (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_null» .Null .Null⟩)
      start (.success (.of true)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_null_clauses» .Null .Null) ())
    start (.success (.of true)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_null:clause:0» .Null .Null)
      start .unmatch start
    unfold SpecTec.«$match_null:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by decide)
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_null:clause:1» .Null .Null)
      start (.success (.of true)) start
    unfold SpecTec.«$match_null:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · exact SpecTecExecution.Eval.pure true

theorem match_null_null_no_null (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_null» .Null .NoNull⟩)
      start (.success (.of false)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_null_clauses» .Null .NoNull) ())
    start (.success (.of false)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_null:clause:0» .Null .NoNull)
      start .unmatch start
    unfold SpecTec.«$match_null:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by decide)
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_null:clause:1» .Null .NoNull)
        start .unmatch start
      unfold SpecTec.«$match_null:clause:1»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false (by decide)
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_null:clause:2» .Null .NoNull)
        start (.success (.of false)) start
      exact SpecTecExecution.Eval.pure false

theorem match_null_total (a b : SpecTec.null) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_null» a b⟩)
      start (.success (.of (matchNull a b))) start := by
  cases a <;> cases b <;> simp only [matchNull]
  · exact match_null_no_null_no_null start
  · exact match_null_no_null_null start
  · exact match_null_null_no_null start
  · exact match_null_null_null start

theorem match_null_deterministic (a b : SpecTec.null)
    (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_null» a b⟩)
      start outcome finalSupply) :
    outcome = .success (.of (matchNull a b)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_null_total a b start)

end properties.wasm_module_not_ok.Rejection
