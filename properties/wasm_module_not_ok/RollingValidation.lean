import properties.wasm_module_not_ok.RangeValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

/-- The suffix built by the generated `$rolldt'` recursion. -/
def rolledDefs (rect : SpecTec.rectype) (i count : Nat) : List SpecTec.deftype :=
  match count with
  | 0 => []
  | count + 1 => .DefT rect i :: rolledDefs rect (i + 1) count

theorem rolldt_aux_total_bound (st : List SpecTec.subtype)
    (i fuel start : Nat) (hbound : st.length - i ≤ fuel) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.deftype,
        SpecTec.Call.«$rolldt'» i (.RecT st)⟩)
      start
      (.success (.of (rolledDefs (.RecT st) i (st.length - i))))
      start := by
  induction fuel generalizing i with
  | zero =>
      have hi : ¬ i < st.length := by omega
      have hcount : st.length - i = 0 := by omega
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$rolldt'_clauses» i (.RecT st)))
        start (.success (.of (rolledDefs (.RecT st) i (st.length - i)))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$rolldt':clause:0» i (.RecT st)) start .unmatch start
        unfold SpecTec.«$rolldt':clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false hi
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$rolldt':clause:1» i (.RecT st))
          start (.success (.of (rolledDefs (.RecT st) i (st.length - i)))) start
        simpa [SpecTec.«$rolldt':clause:1», hcount, rolledDefs] using
          (SpecTecExecution.Eval.pure ([] : List SpecTec.deftype) (n := start))
  | succ fuel ih =>
      by_cases hi : i < st.length
      · have hnext : st.length - (i + 1) ≤ fuel := by omega
        have hcount : st.length - i = (st.length - (i + 1)) + 1 := by omega
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.«$rolldt'_clauses» i (.RecT st)))
          start (.success (.of (rolledDefs (.RecT st) i (st.length - i)))) start
        apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$rolldt':clause:0» i (.RecT st))
          start (.success (.of (rolledDefs (.RecT st) i (st.length - i)))) start
        unfold SpecTec.«$rolldt':clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hi
        · apply SpecTecExecution.Eval.bind_success (ih (i + 1) hnext)
          simpa [hcount, rolledDefs] using
            (SpecTecExecution.Eval.pure
              (SpecTec.deftype.DefT (.RecT st) i ::
                rolledDefs (.RecT st) (i + 1) (st.length - (i + 1)))
              (n := start))
      · have hcount : st.length - i = 0 := by omega
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.«$rolldt'_clauses» i (.RecT st)))
          start (.success (.of (rolledDefs (.RecT st) i (st.length - i)))) start
        apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$rolldt':clause:0» i (.RecT st)) start .unmatch start
          unfold SpecTec.«$rolldt':clause:0»
          apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false hi
        · apply SpecTecExecution.tryClauses_cons_success
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$rolldt':clause:1» i (.RecT st))
            start (.success (.of (rolledDefs (.RecT st) i (st.length - i)))) start
          simpa [SpecTec.«$rolldt':clause:1», hcount, rolledDefs] using
            (SpecTecExecution.Eval.pure ([] : List SpecTec.deftype) (n := start))

theorem rolldt_aux_total (st : List SpecTec.subtype) (i start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.deftype,
        SpecTec.Call.«$rolldt'» i (.RecT st)⟩)
      start
      (.success (.of (rolledDefs (.RecT st) i (st.length - i))))
      start :=
  rolldt_aux_total_bound st i (st.length - i) start (Nat.le_refl _)

theorem rolldt_aux_deterministic (st : List SpecTec.subtype)
    (i start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.deftype,
        SpecTec.Call.«$rolldt'» i (.RecT st)⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rolledDefs (.RecT st) i (st.length - i))) ∧
      finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (rolldt_aux_total st i start)

end properties.wasm_module_not_ok.Rejection
