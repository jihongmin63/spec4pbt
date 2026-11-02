import properties.wasm_module_not_ok.SubtypeRollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollSubtypes (ts : List SpecTec.subtype) (x y : Nat) :
    List SpecTec.subtype :=
  ts.map (fun t => rollSubtype t x y)

theorem subst_subtype_list_roll_total (ts : List SpecTec.subtype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.subtype,
        SpecTec.Call.«$subst_rectype:case_1:iter:0»
          (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» ts⟩)
      start (.success (.of (rollSubtypes ts x y))) start := by
  induction ts with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_rectype:case_1:iter:0_clauses»
            (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» []))
        start (.success (.of (rollSubtypes [] x y))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
          (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» [])
        start (.success (.of (rollSubtypes [] x y))) start
      simpa [SpecTec.«$subst_rectype:case_1:iter:0:clause:0»,
        rollSubtypes] using
        (SpecTecExecution.Eval.pure ([] : List SpecTec.subtype) (n := start))
  | cons t ts ih =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_rectype:case_1:iter:0_clauses»
            (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» (t :: ts)))
        start (.success (.of (rollSubtypes (t :: ts) x y))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
            (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» (t :: ts))
          start .unmatch start
        unfold SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_rectype:case_1:iter:0:clause:1»
            (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» (t :: ts))
          start (.success (.of (rollSubtypes (t :: ts) x y))) start
        unfold SpecTec.«$subst_rectype:case_1:iter:0:clause:1»
        apply SpecTecExecution.Eval.bind_success
          (subst_subtype_roll_total t x y start)
        apply SpecTecExecution.Eval.bind_success ih
        simpa [rollSubtypes] using
          (SpecTecExecution.Eval.pure
            (rollSubtype t x y :: rollSubtypes ts x y) (n := start))

theorem subst_subtype_list_roll_deterministic (ts : List SpecTec.subtype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.subtype,
        SpecTec.Call.«$subst_rectype:case_1:iter:0»
          (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» ts⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollSubtypes ts x y)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_subtype_list_roll_total ts x y start)

end properties.wasm_module_not_ok.Rejection
