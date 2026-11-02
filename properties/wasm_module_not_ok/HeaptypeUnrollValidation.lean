import properties.wasm_module_not_ok.UnrollSubstitutionLeaf
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollHeaptype (ht : SpecTec.heaptype) (rect : SpecTec.rectype) : SpecTec.heaptype :=
  match ht with
  | .VarHT tv => unrollTypevar tv rect
  | other => other

private theorem subst_heaptype_fixed_total (ht : SpecTec.heaptype)
    (rect : SpecTec.rectype) (start : Nat)
    (hfixed :
      ht = .AnyHT ∨ ht = .NoneHT ∨ ht = .EqHT ∨
      ht = .I31HT ∨ ht = .StructHT ∨ ht = .ArrayHT ∨
      ht = .FuncHT ∨ ht = .NoFuncHT ∨ ht = .ExnHT ∨
      ht = .NoExnHT ∨ ht = .ExternHT ∨ ht = .NoExternHT ∨
      ht = .BotHT) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_heaptype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» ht⟩)
      start (.success (.of ht)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$subst_heaptype_clauses» SpecTec.rectype rect
        SpecTec.Call.«$s_unroll» ht))
    start (.success (.of ht)) start
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$subst_heaptype:clause:0» SpecTec.rectype rect
      SpecTec.Call.«$s_unroll» ht)
    start (.success (.of ht)) start
  unfold SpecTec.«$subst_heaptype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by simpa only [or_assoc] using hfixed)
  · exact SpecTecExecution.Eval.pure ht

private theorem subst_heaptype_var_total (tv : SpecTec.typevar)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_heaptype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» (.VarHT tv)⟩)
      start (.success (.of (unrollTypevar tv rect))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$subst_heaptype_clauses» SpecTec.rectype rect
        SpecTec.Call.«$s_unroll» (.VarHT tv)))
    start (.success (.of (unrollTypevar tv rect))) start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$subst_heaptype:clause:0» SpecTec.rectype rect
        SpecTec.Call.«$s_unroll» (.VarHT tv)) start .unmatch start
    unfold SpecTec.«$subst_heaptype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simp)
  · apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$subst_heaptype:clause:1» SpecTec.rectype rect
        SpecTec.Call.«$s_unroll» (.VarHT tv))
      start (.success (.of (unrollTypevar tv rect))) start
    unfold SpecTec.«$subst_heaptype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«sub:heaptype:heaptypeVar»])
    · simp only [SpecTec.«$subst_heaptype:case_2:downcast:0»]
      apply SpecTecExecution.Eval.bind_success (s_unroll_total tv rect start)
      exact SpecTecExecution.Eval.pure (unrollTypevar tv rect)

private theorem subst_heaptype_def_total (dt : SpecTec.deftype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_heaptype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» (.DefHT dt)⟩)
      start (.success (.of (SpecTec.heaptype.DefHT dt))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$subst_heaptype_clauses» SpecTec.rectype rect
        SpecTec.Call.«$s_unroll» (.DefHT dt)))
    start (.success (.of (SpecTec.heaptype.DefHT dt))) start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$subst_heaptype:clause:0» SpecTec.rectype rect
        SpecTec.Call.«$s_unroll» (.DefHT dt)) start .unmatch start
    unfold SpecTec.«$subst_heaptype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simp)
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_heaptype:clause:1» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» (.DefHT dt)) start .unmatch start
      unfold SpecTec.«$subst_heaptype:clause:1»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«sub:heaptype:heaptypeVar»])
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_heaptype:clause:2» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» (.DefHT dt))
        start (.success (.of (SpecTec.heaptype.DefHT dt))) start
      unfold SpecTec.«$subst_heaptype:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:heaptype:DefHT»])
      · exact SpecTecExecution.Eval.pure (SpecTec.heaptype.DefHT dt)

theorem subst_heaptype_unroll_total (ht : SpecTec.heaptype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_heaptype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» ht⟩)
      start (.success (.of (unrollHeaptype ht rect))) start := by
  cases ht with
  | VarHT tv => exact subst_heaptype_var_total tv rect start
  | DefHT dt => exact subst_heaptype_def_total dt rect start
  | AnyHT => exact subst_heaptype_fixed_total .AnyHT rect start (by simp)
  | NoneHT => exact subst_heaptype_fixed_total .NoneHT rect start (by simp)
  | EqHT => exact subst_heaptype_fixed_total .EqHT rect start (by simp)
  | I31HT => exact subst_heaptype_fixed_total .I31HT rect start (by simp)
  | StructHT => exact subst_heaptype_fixed_total .StructHT rect start (by simp)
  | ArrayHT => exact subst_heaptype_fixed_total .ArrayHT rect start (by simp)
  | FuncHT => exact subst_heaptype_fixed_total .FuncHT rect start (by simp)
  | NoFuncHT => exact subst_heaptype_fixed_total .NoFuncHT rect start (by simp)
  | ExnHT => exact subst_heaptype_fixed_total .ExnHT rect start (by simp)
  | NoExnHT => exact subst_heaptype_fixed_total .NoExnHT rect start (by simp)
  | ExternHT => exact subst_heaptype_fixed_total .ExternHT rect start (by simp)
  | NoExternHT => exact subst_heaptype_fixed_total .NoExternHT rect start (by simp)
  | BotHT => exact subst_heaptype_fixed_total .BotHT rect start (by simp)

theorem subst_heaptype_unroll_deterministic (ht : SpecTec.heaptype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_heaptype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» ht⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollHeaptype ht rect)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_heaptype_unroll_total ht rect start)

end properties.wasm_module_not_ok.Rejection
