import properties.wasm_module_not_ok.CompoundRollValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollStrtype (strt : SpecTec.strtype) (x y : Nat) : SpecTec.strtype :=
  match strt with
  | .DefStructT st => .DefStructT (rollStructtype st x y)
  | .DefArrayT arrayTy => .DefArrayT (rollArraytype arrayTy x y)
  | .DefFuncT ft => .DefFuncT (rollFunctype ft x y)

theorem subst_strtype_roll_total (strt : SpecTec.strtype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype,
        SpecTec.SpecTecCall.«$subst_strtype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» strt⟩)
      start (.success (.of (rollStrtype strt x y))) start := by
  cases strt with
  | DefStructT st =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_strtype_clauses» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.DefStructT st)) ())
        start (.success (.of (rollStrtype (.DefStructT st) x y))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_strtype:clause:0» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» (.DefStructT st))
        start (.success (.of (rollStrtype (.DefStructT st) x y))) start
      unfold SpecTec.«$subst_strtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:strtype:DefStructT»])
      · apply SpecTecExecution.Eval.bind_success
          (subst_structtype_roll_total st x y start)
        exact SpecTecExecution.Eval.pure
          (SpecTec.strtype.DefStructT (rollStructtype st x y))
  | DefArrayT arrayTy =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_strtype_clauses» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.DefArrayT arrayTy)) ())
        start (.success (.of (rollStrtype (.DefArrayT arrayTy) x y))) start
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_strtype:clause:0» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.DefArrayT arrayTy)) start .unmatch start
        unfold SpecTec.«$subst_strtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefStructT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_strtype:clause:1» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.DefArrayT arrayTy))
          start (.success (.of (rollStrtype (.DefArrayT arrayTy) x y))) start
        unfold SpecTec.«$subst_strtype:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
        · apply SpecTecExecution.Eval.bind_success
            (subst_arraytype_roll_total arrayTy x y start)
          exact SpecTecExecution.Eval.pure
            (SpecTec.strtype.DefArrayT (rollArraytype arrayTy x y))
  | DefFuncT ft =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_strtype_clauses» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.DefFuncT ft)) ())
        start (.success (.of (rollStrtype (.DefFuncT ft) x y))) start
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_strtype:clause:0» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.DefFuncT ft)) start .unmatch start
        unfold SpecTec.«$subst_strtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefStructT»])
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_strtype:clause:1» (Nat × Nat) (x, y)
              SpecTec.SpecTecCall.«$s_roll» (.DefFuncT ft)) start .unmatch start
          unfold SpecTec.«$subst_strtype:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
        · apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_strtype:clause:2» (Nat × Nat) (x, y)
              SpecTec.SpecTecCall.«$s_roll» (.DefFuncT ft))
            start (.success (.of (rollStrtype (.DefFuncT ft) x y))) start
          unfold SpecTec.«$subst_strtype:clause:2»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true
              (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
          · apply SpecTecExecution.Eval.bind_success
              (subst_functype_roll_total ft x y start)
            exact SpecTecExecution.Eval.pure
              (SpecTec.strtype.DefFuncT (rollFunctype ft x y))

theorem subst_strtype_roll_deterministic (strt : SpecTec.strtype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype,
        SpecTec.SpecTecCall.«$subst_strtype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» strt⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollStrtype strt x y)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_strtype_roll_total strt x y start)

end properties.wasm_module_not_ok.Rejection
