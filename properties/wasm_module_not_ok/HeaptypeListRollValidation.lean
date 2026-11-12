import properties.wasm_module_not_ok.StrtypeRollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollHeaptypes (ts : List SpecTec.heaptype) (x y : Nat) :
    List SpecTec.heaptype :=
  ts.map (fun t => rollHeaptype t x y)

theorem subst_heaptype_list_roll_total (ts : List SpecTec.heaptype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.heaptype,
        SpecTec.Call.«$subst_subtype:case_1:iter:0»
          (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» ts⟩)
      start (.success (.of (rollHeaptypes ts x y))) start := by
  induction ts with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_subtype:case_1:iter:0_clauses»
            (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» []))
        start (.success (.of (rollHeaptypes [] x y))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
          (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» [])
        start (.success (.of (rollHeaptypes [] x y))) start
      simpa [SpecTec.«$subst_subtype:case_1:iter:0:clause:0»,
        rollHeaptypes] using
        (SpecTecExecution.Eval.pure ([] : List SpecTec.heaptype) (n := start))
  | cons t ts ih =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_subtype:case_1:iter:0_clauses»
            (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» (t :: ts)))
        start (.success (.of (rollHeaptypes (t :: ts) x y))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
            (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» (t :: ts))
          start .unmatch start
        unfold SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_subtype:case_1:iter:0:clause:1»
            (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» (t :: ts))
          start (.success (.of (rollHeaptypes (t :: ts) x y))) start
        unfold SpecTec.«$subst_subtype:case_1:iter:0:clause:1»
        apply SpecTecExecution.Eval.bind_success
          (subst_heaptype_roll_total t x y start)
        apply SpecTecExecution.Eval.bind_success ih
        simpa [rollHeaptypes] using
          (SpecTecExecution.Eval.pure
            (rollHeaptype t x y :: rollHeaptypes ts x y) (n := start))

theorem subst_heaptype_list_roll_deterministic (ts : List SpecTec.heaptype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.heaptype,
        SpecTec.Call.«$subst_subtype:case_1:iter:0»
          (Nat × Nat) (x, y) SpecTec.Call.«$s_roll» ts⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollHeaptypes ts x y)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_heaptype_list_roll_total ts x y start)

end properties.wasm_module_not_ok.Rejection
