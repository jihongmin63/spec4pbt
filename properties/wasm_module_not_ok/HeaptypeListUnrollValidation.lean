import properties.wasm_module_not_ok.StrtypeUnrollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollHeaptypes (ts : List SpecTec.heaptype) (rect : SpecTec.rectype) :
    List SpecTec.heaptype :=
  ts.map (fun t => unrollHeaptype t rect)

theorem subst_heaptype_list_unroll_total (ts : List SpecTec.heaptype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.heaptype,
        SpecTec.Call.«$subst_subtype:case_1:iter:0»
          SpecTec.rectype rect SpecTec.Call.«$s_unroll» ts⟩)
      start (.success (.of (unrollHeaptypes ts rect))) start := by
  induction ts with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_subtype:case_1:iter:0_clauses»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» []))
        start (.success (.of (unrollHeaptypes [] rect))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
          SpecTec.rectype rect SpecTec.Call.«$s_unroll» [])
        start (.success (.of (unrollHeaptypes [] rect))) start
      simpa [SpecTec.«$subst_subtype:case_1:iter:0:clause:0»,
        unrollHeaptypes] using
        (SpecTecExecution.Eval.pure ([] : List SpecTec.heaptype) (n := start))
  | cons t ts ih =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_subtype:case_1:iter:0_clauses»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» (t :: ts)))
        start (.success (.of (unrollHeaptypes (t :: ts) rect))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» (t :: ts))
          start .unmatch start
        unfold SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_subtype:case_1:iter:0:clause:1»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» (t :: ts))
          start (.success (.of (unrollHeaptypes (t :: ts) rect))) start
        unfold SpecTec.«$subst_subtype:case_1:iter:0:clause:1»
        apply SpecTecExecution.Eval.bind_success
          (subst_heaptype_unroll_total t rect start)
        apply SpecTecExecution.Eval.bind_success ih
        simpa [unrollHeaptypes] using
          (SpecTecExecution.Eval.pure
            (unrollHeaptype t rect :: unrollHeaptypes ts rect) (n := start))

theorem subst_heaptype_list_unroll_deterministic (ts : List SpecTec.heaptype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.heaptype,
        SpecTec.Call.«$subst_subtype:case_1:iter:0»
          SpecTec.rectype rect SpecTec.Call.«$s_unroll» ts⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollHeaptypes ts rect)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_heaptype_list_unroll_total ts rect start)

end properties.wasm_module_not_ok.Rejection
