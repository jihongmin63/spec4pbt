import properties.wasm_module_not_ok.ValtypeListRollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem subst_resulttype_roll_total (ts : SpecTec.resulttype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.resulttype,
        SpecTec.Call.«$subst_resulttype» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» ts⟩)
      start (.success (.of (rollValtypes ts x y))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$subst_resulttype_clauses» (Nat × Nat) (x, y)
        SpecTec.Call.«$s_roll» ts))
    start (.success (.of (rollValtypes ts x y))) start
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$subst_resulttype:clause:0» (Nat × Nat) (x, y)
      SpecTec.Call.«$s_roll» ts)
    start (.success (.of (rollValtypes ts x y))) start
  unfold SpecTec.«$subst_resulttype:clause:0»
  apply SpecTecExecution.Eval.bind_success
    (subst_valtype_list_roll_total ts x y start)
  exact SpecTecExecution.Eval.pure (rollValtypes ts x y)

def rollFunctype (ft : SpecTec.functype) (x y : Nat) : SpecTec.functype :=
  match ft with
  | .FuncT params results =>
      .FuncT (rollValtypes params x y) (rollValtypes results x y)

theorem subst_functype_roll_total (ft : SpecTec.functype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.functype,
        SpecTec.Call.«$subst_functype» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» ft⟩)
      start (.success (.of (rollFunctype ft x y))) start := by
  cases ft with
  | FuncT params results =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_functype_clauses» (Nat × Nat) (x, y)
            SpecTec.Call.«$s_roll» (.FuncT params results)))
        start (.success (.of
          (rollFunctype (.FuncT params results) x y))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_functype:clause:0» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» (.FuncT params results))
        start (.success (.of
          (rollFunctype (.FuncT params results) x y))) start
      unfold SpecTec.«$subst_functype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_resulttype_roll_total params x y start)
      apply SpecTecExecution.Eval.bind_success
        (subst_resulttype_roll_total results x y start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.functype.FuncT
          (rollValtypes params x y) (rollValtypes results x y))

theorem subst_functype_roll_deterministic (ft : SpecTec.functype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.functype,
        SpecTec.Call.«$subst_functype» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» ft⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollFunctype ft x y)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_functype_roll_total ft x y start)

end properties.wasm_module_not_ok.Rejection
