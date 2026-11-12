import properties.wasm_module_not_ok.SubtypeUnrollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollSubtypes (ts : List SpecTec.subtype) (rect : SpecTec.rectype) :
    List SpecTec.subtype :=
  ts.map (fun t => unrollSubtype t rect)

theorem subst_subtype_list_unroll_total (ts : List SpecTec.subtype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.subtype,
        SpecTec.Call.«$subst_rectype:case_1:iter:0»
          SpecTec.rectype rect SpecTec.Call.«$s_unroll» ts⟩)
      start (.success (.of (unrollSubtypes ts rect))) start := by
  induction ts with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_rectype:case_1:iter:0_clauses»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» []))
        start (.success (.of (unrollSubtypes [] rect))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
          SpecTec.rectype rect SpecTec.Call.«$s_unroll» [])
        start (.success (.of (unrollSubtypes [] rect))) start
      simpa [SpecTec.«$subst_rectype:case_1:iter:0:clause:0»,
        unrollSubtypes] using
        (SpecTecExecution.Eval.pure ([] : List SpecTec.subtype) (n := start))
  | cons t ts ih =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_rectype:case_1:iter:0_clauses»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» (t :: ts)))
        start (.success (.of (unrollSubtypes (t :: ts) rect))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» (t :: ts))
          start .unmatch start
        unfold SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_rectype:case_1:iter:0:clause:1»
            SpecTec.rectype rect SpecTec.Call.«$s_unroll» (t :: ts))
          start (.success (.of (unrollSubtypes (t :: ts) rect))) start
        unfold SpecTec.«$subst_rectype:case_1:iter:0:clause:1»
        apply SpecTecExecution.Eval.bind_success
          (subst_subtype_unroll_total t rect start)
        apply SpecTecExecution.Eval.bind_success ih
        simpa [unrollSubtypes] using
          (SpecTecExecution.Eval.pure
            (unrollSubtype t rect :: unrollSubtypes ts rect) (n := start))

theorem subst_subtype_list_unroll_deterministic (ts : List SpecTec.subtype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.subtype,
        SpecTec.Call.«$subst_rectype:case_1:iter:0»
          SpecTec.rectype rect SpecTec.Call.«$s_unroll» ts⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollSubtypes ts rect)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_subtype_list_unroll_total ts rect start)

end properties.wasm_module_not_ok.Rejection
