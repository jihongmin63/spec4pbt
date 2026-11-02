import properties.wasm_module_not_ok.RollSubstitutionLeaf

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollHeaptype (ht : SpecTec.heaptype) (x y : Nat) : SpecTec.heaptype :=
  match ht with
  | .VarHT tv => rollTypevar tv x y
  | other => other

private theorem subst_heaptype_fixed_total (ht : SpecTec.heaptype)
    (x y start : Nat)
    (hfixed :
      ht = .AnyHT ∨ ht = .NoneHT ∨ ht = .EqHT ∨
      ht = .I31HT ∨ ht = .StructHT ∨ ht = .ArrayHT ∨
      ht = .FuncHT ∨ ht = .NoFuncHT ∨ ht = .ExnHT ∨
      ht = .NoExnHT ∨ ht = .ExternHT ∨ ht = .NoExternHT ∨
      ht = .BotHT) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$subst_heaptype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» ht⟩)
      start (.success (.of ht)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$subst_heaptype_clauses» (Nat × Nat) (x, y)
        SpecTec.SpecTecCall.«$s_roll» ht) ())
    start (.success (.of ht)) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$subst_heaptype:clause:0» (Nat × Nat) (x, y)
      SpecTec.SpecTecCall.«$s_roll» ht)
    start (.success (.of ht)) start
  unfold SpecTec.«$subst_heaptype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by simpa only [or_assoc] using hfixed)
  · exact SpecTecExecution.Eval.pure ht

private theorem subst_heaptype_var_total (tv : SpecTec.typevar)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$subst_heaptype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» (.VarHT tv)⟩)
      start (.success (.of (rollTypevar tv x y))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$subst_heaptype_clauses» (Nat × Nat) (x, y)
        SpecTec.SpecTecCall.«$s_roll» (.VarHT tv)) ())
    start (.success (.of (rollTypevar tv x y))) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$subst_heaptype:clause:0» (Nat × Nat) (x, y)
        SpecTec.SpecTecCall.«$s_roll» (.VarHT tv)) start .unmatch start
    unfold SpecTec.«$subst_heaptype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simp)
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$subst_heaptype:clause:1» (Nat × Nat) (x, y)
        SpecTec.SpecTecCall.«$s_roll» (.VarHT tv))
      start (.success (.of (rollTypevar tv x y))) start
    unfold SpecTec.«$subst_heaptype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«sub:heaptype:heaptypeVar»])
    · simp only [SpecTec.«$subst_heaptype:case_2:downcast:0»]
      apply SpecTecExecution.Eval.bind_success (s_roll_total tv x y start)
      exact SpecTecExecution.Eval.pure (rollTypevar tv x y)

private theorem subst_heaptype_def_total (dt : SpecTec.deftype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$subst_heaptype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» (.DefHT dt)⟩)
      start (.success (.of (SpecTec.heaptype.DefHT dt))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$subst_heaptype_clauses» (Nat × Nat) (x, y)
        SpecTec.SpecTecCall.«$s_roll» (.DefHT dt)) ())
    start (.success (.of (SpecTec.heaptype.DefHT dt))) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$subst_heaptype:clause:0» (Nat × Nat) (x, y)
        SpecTec.SpecTecCall.«$s_roll» (.DefHT dt)) start .unmatch start
    unfold SpecTec.«$subst_heaptype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simp)
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_heaptype:clause:1» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» (.DefHT dt)) start .unmatch start
      unfold SpecTec.«$subst_heaptype:clause:1»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«sub:heaptype:heaptypeVar»])
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_heaptype:clause:2» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» (.DefHT dt))
        start (.success (.of (SpecTec.heaptype.DefHT dt))) start
      unfold SpecTec.«$subst_heaptype:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:heaptype:DefHT»])
      · exact SpecTecExecution.Eval.pure (SpecTec.heaptype.DefHT dt)

theorem subst_heaptype_roll_total (ht : SpecTec.heaptype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$subst_heaptype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» ht⟩)
      start (.success (.of (rollHeaptype ht x y))) start := by
  cases ht with
  | VarHT tv => exact subst_heaptype_var_total tv x y start
  | DefHT dt => exact subst_heaptype_def_total dt x y start
  | AnyHT => exact subst_heaptype_fixed_total .AnyHT x y start (by simp)
  | NoneHT => exact subst_heaptype_fixed_total .NoneHT x y start (by simp)
  | EqHT => exact subst_heaptype_fixed_total .EqHT x y start (by simp)
  | I31HT => exact subst_heaptype_fixed_total .I31HT x y start (by simp)
  | StructHT => exact subst_heaptype_fixed_total .StructHT x y start (by simp)
  | ArrayHT => exact subst_heaptype_fixed_total .ArrayHT x y start (by simp)
  | FuncHT => exact subst_heaptype_fixed_total .FuncHT x y start (by simp)
  | NoFuncHT => exact subst_heaptype_fixed_total .NoFuncHT x y start (by simp)
  | ExnHT => exact subst_heaptype_fixed_total .ExnHT x y start (by simp)
  | NoExnHT => exact subst_heaptype_fixed_total .NoExnHT x y start (by simp)
  | ExternHT => exact subst_heaptype_fixed_total .ExternHT x y start (by simp)
  | NoExternHT => exact subst_heaptype_fixed_total .NoExternHT x y start (by simp)
  | BotHT => exact subst_heaptype_fixed_total .BotHT x y start (by simp)

theorem subst_heaptype_roll_deterministic (ht : SpecTec.heaptype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.heaptype,
        SpecTec.SpecTecCall.«$subst_heaptype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» ht⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollHeaptype ht x y)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_heaptype_roll_total ht x y start)

end properties.wasm_module_not_ok.Rejection
