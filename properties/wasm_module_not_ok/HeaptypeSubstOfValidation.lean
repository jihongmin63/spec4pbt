import properties.wasm_module_not_ok.SubstOfResult
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substHeaptypeResult (ht : SpecTec.heaptype)
    (dts : List SpecTec.deftype) : Option SpecTec.heaptype :=
  match ht with
  | .VarHT tv => substOfResult tv dts
  | other => some other

private theorem subst_heaptype_fixed_of_total (ht : SpecTec.heaptype)
    (dts : List SpecTec.deftype) (start : Nat)
    (hfixed :
      ht = .AnyHT ∨ ht = .NoneHT ∨ ht = .EqHT ∨
      ht = .I31HT ∨ ht = .StructHT ∨ ht = .ArrayHT ∨
      ht = .FuncHT ∨ ht = .NoFuncHT ∨ ht = .ExnHT ∨
      ht = .NoExnHT ∨ ht = .ExternHT ∨ ht = .NoExternHT ∨
      ht = .BotHT) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_heaptype» (List SpecTec.deftype) dts
          SpecTec.Call.«$subst_of» ht⟩)
      start (.success (.of ht)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$subst_heaptype_clauses» (List SpecTec.deftype) dts
        SpecTec.Call.«$subst_of» ht))
    start (.success (.of ht)) start
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$subst_heaptype:clause:0» (List SpecTec.deftype) dts
      SpecTec.Call.«$subst_of» ht)
    start (.success (.of ht)) start
  unfold SpecTec.«$subst_heaptype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by simpa only [or_assoc] using hfixed)
  · exact SpecTecExecution.Eval.pure ht

private theorem subst_heaptype_def_of_total (dt : SpecTec.deftype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_heaptype» (List SpecTec.deftype) dts
          SpecTec.Call.«$subst_of» (.DefHT dt)⟩)
      start (.success (.of (SpecTec.heaptype.DefHT dt))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$subst_heaptype_clauses» (List SpecTec.deftype) dts
        SpecTec.Call.«$subst_of» (.DefHT dt)))
    start (.success (.of (SpecTec.heaptype.DefHT dt))) start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$subst_heaptype:clause:0» (List SpecTec.deftype) dts
        SpecTec.Call.«$subst_of» (.DefHT dt)) start .unmatch start
    unfold SpecTec.«$subst_heaptype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simp)
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_heaptype:clause:1» (List SpecTec.deftype) dts
          SpecTec.Call.«$subst_of» (.DefHT dt)) start .unmatch start
      unfold SpecTec.«$subst_heaptype:clause:1»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«sub:heaptype:heaptypeVar»])
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_heaptype:clause:2» (List SpecTec.deftype) dts
          SpecTec.Call.«$subst_of» (.DefHT dt))
        start (.success (.of (SpecTec.heaptype.DefHT dt))) start
      unfold SpecTec.«$subst_heaptype:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:heaptype:DefHT»])
      · exact SpecTecExecution.Eval.pure (SpecTec.heaptype.DefHT dt)


private theorem subst_heaptype_var_of_some (tv : SpecTec.typevar)
    (dts : List SpecTec.deftype) (result : SpecTec.heaptype)
    (start : Nat) (hresult : substOfResult tv dts = some result) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_heaptype»
          (List SpecTec.deftype) dts
          SpecTec.Call.«$subst_of» (.VarHT tv)⟩)
      start (.success (.of result)) start := by
  have hleaf : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_of» tv dts⟩)
      start (.success (.of result)) start := by
    simpa [optionOutcome, hresult] using subst_of_total_result tv dts start
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$subst_heaptype_clauses» (List SpecTec.deftype) dts
        SpecTec.Call.«$subst_of» (.VarHT tv)))
    start (.success (.of result)) start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$subst_heaptype:clause:0» (List SpecTec.deftype) dts
        SpecTec.Call.«$subst_of» (.VarHT tv)) start .unmatch start
    unfold SpecTec.«$subst_heaptype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simp)
  · apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$subst_heaptype:clause:1» (List SpecTec.deftype) dts
        SpecTec.Call.«$subst_of» (.VarHT tv))
      start (.success (.of result)) start
    unfold SpecTec.«$subst_heaptype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«sub:heaptype:heaptypeVar»])
    · simp only [SpecTec.«$subst_heaptype:case_2:downcast:0»]
      apply SpecTecExecution.Eval.bind_success hleaf
      exact SpecTecExecution.Eval.pure result

private theorem subst_heaptype_var_of_none (tv : SpecTec.typevar)
    (dts : List SpecTec.deftype) (start : Nat)
    (hresult : substOfResult tv dts = none) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_heaptype»
          (List SpecTec.deftype) dts
          SpecTec.Call.«$subst_of» (.VarHT tv)⟩)
      start .unmatch start := by
  have hleaf : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_of» tv dts⟩)
      start .unmatch start := by
    simpa [optionOutcome, hresult] using subst_of_total_result tv dts start
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$subst_heaptype_clauses» (List SpecTec.deftype) dts
        SpecTec.Call.«$subst_of» (.VarHT tv)))
    start .unmatch start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$subst_heaptype:clause:0» (List SpecTec.deftype) dts
        SpecTec.Call.«$subst_of» (.VarHT tv)) start .unmatch start
    unfold SpecTec.«$subst_heaptype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simp)
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_heaptype:clause:1» (List SpecTec.deftype) dts
          SpecTec.Call.«$subst_of» (.VarHT tv))
        start .unmatch start
      unfold SpecTec.«$subst_heaptype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«sub:heaptype:heaptypeVar»])
      · simp only [SpecTec.«$subst_heaptype:case_2:downcast:0»]
        apply SpecTecExecution.Eval.bind_unmatch hleaf
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_heaptype:clause:2» (List SpecTec.deftype) dts
            SpecTec.Call.«$subst_of» (.VarHT tv))
          start .unmatch start
        unfold SpecTec.«$subst_heaptype:clause:2»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:heaptype:DefHT»])
      · exact SpecTecExecution.tryClauses_nil start

theorem subst_heaptype_of_total (ht : SpecTec.heaptype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_heaptype»
          (List SpecTec.deftype) dts
          SpecTec.Call.«$subst_of» ht⟩)
      start (optionOutcome (substHeaptypeResult ht dts)) start := by
  cases ht with
  | VarHT tv =>
      cases hresult : substOfResult tv dts with
      | none =>
          simpa [substHeaptypeResult, optionOutcome, hresult] using
            subst_heaptype_var_of_none tv dts start hresult
      | some result =>
          simpa [substHeaptypeResult, optionOutcome, hresult] using
            subst_heaptype_var_of_some tv dts result start hresult
  | DefHT dt =>
      simpa [substHeaptypeResult, optionOutcome] using
        subst_heaptype_def_of_total dt dts start
  | AnyHT => exact subst_heaptype_fixed_of_total .AnyHT dts start (by simp)
  | NoneHT => exact subst_heaptype_fixed_of_total .NoneHT dts start (by simp)
  | EqHT => exact subst_heaptype_fixed_of_total .EqHT dts start (by simp)
  | I31HT => exact subst_heaptype_fixed_of_total .I31HT dts start (by simp)
  | StructHT => exact subst_heaptype_fixed_of_total .StructHT dts start (by simp)
  | ArrayHT => exact subst_heaptype_fixed_of_total .ArrayHT dts start (by simp)
  | FuncHT => exact subst_heaptype_fixed_of_total .FuncHT dts start (by simp)
  | NoFuncHT => exact subst_heaptype_fixed_of_total .NoFuncHT dts start (by simp)
  | ExnHT => exact subst_heaptype_fixed_of_total .ExnHT dts start (by simp)
  | NoExnHT => exact subst_heaptype_fixed_of_total .NoExnHT dts start (by simp)
  | ExternHT => exact subst_heaptype_fixed_of_total .ExternHT dts start (by simp)
  | NoExternHT => exact subst_heaptype_fixed_of_total .NoExternHT dts start (by simp)
  | BotHT => exact subst_heaptype_fixed_of_total .BotHT dts start (by simp)

theorem subst_heaptype_of_deterministic (ht : SpecTec.heaptype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_heaptype»
          (List SpecTec.deftype) dts
          SpecTec.Call.«$subst_of» ht⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substHeaptypeResult ht dts) ∧
      finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_heaptype_of_total ht dts start)

end properties.wasm_module_not_ok.Rejection
