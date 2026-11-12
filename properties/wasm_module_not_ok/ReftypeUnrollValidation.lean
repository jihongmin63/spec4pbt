import properties.wasm_module_not_ok.HeaptypeUnrollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollReftype (rt : SpecTec.reftype) (rect : SpecTec.rectype) : SpecTec.reftype :=
  match rt with
  | .«% %» null ht => .«% %» null (unrollHeaptype ht rect)

theorem subst_reftype_unroll_total (rt : SpecTec.reftype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.reftype,
        SpecTec.Call.«$subst_reftype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» rt⟩)
      start (.success (.of (unrollReftype rt rect))) start := by
  cases rt with
  | «% %» null ht =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_reftype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.«% %» null ht)))
        start (.success (.of (unrollReftype (.«% %» null ht) rect))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_reftype:clause:0» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» (.«% %» null ht))
        start (.success (.of (unrollReftype (.«% %» null ht) rect))) start
      unfold SpecTec.«$subst_reftype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_heaptype_unroll_total ht rect start)
      simpa [unrollReftype] using
        (SpecTecExecution.Eval.pure
          (SpecTec.reftype.«% %» null (unrollHeaptype ht rect)) (n := start))

theorem subst_reftype_unroll_deterministic (rt : SpecTec.reftype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.reftype,
        SpecTec.Call.«$subst_reftype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» rt⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollReftype rt rect)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_reftype_unroll_total rt rect start)

end properties.wasm_module_not_ok.Rejection
