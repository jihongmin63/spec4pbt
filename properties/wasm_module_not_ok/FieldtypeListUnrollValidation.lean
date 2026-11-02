import properties.wasm_module_not_ok.StorageUnrollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollFieldtypes (ts : List SpecTec.fieldtype) (rect : SpecTec.rectype) :
    List SpecTec.fieldtype :=
  ts.map (fun t => unrollFieldtype t rect)

theorem subst_fieldtype_list_unroll_total (ts : List SpecTec.fieldtype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.fieldtype,
        SpecTec.Call.«$subst_structtype:case_1:iter:0»
          SpecTec.rectype rect SpecTec.Call.«$s_unroll» ts⟩)
      start (.success (.of (unrollFieldtypes ts rect))) start := by
  induction ts with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_structtype:case_1:iter:0_clauses»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» []))
        start (.success (.of (unrollFieldtypes [] rect))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
          SpecTec.rectype rect SpecTec.Call.«$s_unroll» [])
        start (.success (.of (unrollFieldtypes [] rect))) start
      simpa [SpecTec.«$subst_structtype:case_1:iter:0:clause:0»,
        unrollFieldtypes] using
        (SpecTecExecution.Eval.pure ([] : List SpecTec.fieldtype) (n := start))
  | cons t ts ih =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_structtype:case_1:iter:0_clauses»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» (t :: ts)))
        start (.success (.of (unrollFieldtypes (t :: ts) rect))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» (t :: ts))
          start .unmatch start
        unfold SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_structtype:case_1:iter:0:clause:1»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» (t :: ts))
          start (.success (.of (unrollFieldtypes (t :: ts) rect))) start
        unfold SpecTec.«$subst_structtype:case_1:iter:0:clause:1»
        apply SpecTecExecution.Eval.bind_success
          (subst_fieldtype_unroll_total t rect start)
        apply SpecTecExecution.Eval.bind_success ih
        simpa [unrollFieldtypes] using
          (SpecTecExecution.Eval.pure
            (unrollFieldtype t rect :: unrollFieldtypes ts rect) (n := start))

theorem subst_fieldtype_list_unroll_deterministic (ts : List SpecTec.fieldtype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.fieldtype,
        SpecTec.Call.«$subst_structtype:case_1:iter:0»
          SpecTec.rectype rect SpecTec.Call.«$s_unroll» ts⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollFieldtypes ts rect)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_fieldtype_list_unroll_total ts rect start)

end properties.wasm_module_not_ok.Rejection
