import properties.wasm_module_not_ok.ReftypeRollValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollValtype (t : SpecTec.valtype) (x y : Nat) : SpecTec.valtype :=
  match t with
  | .RefT rt => .RefT (rollReftype rt x y)
  | other => other

theorem subst_valtype_roll_total (t : SpecTec.valtype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.valtype,
        SpecTec.SpecTecCall.«$subst_valtype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» t⟩)
      start (.success (.of (rollValtype t x y))) start := by
  cases t with
  | NumT nt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_valtype_clauses» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.NumT nt)) ())
        start (.success (.of (rollValtype (.NumT nt) x y))) start
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_valtype:clause:0» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» (.NumT nt))
        start (.success (.of (rollValtype (.NumT nt) x y))) start
      unfold SpecTec.«$subst_valtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:valtype:NumT»])
      · exact SpecTecExecution.Eval.pure (SpecTec.valtype.NumT nt)
  | VecT vt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_valtype_clauses» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.VecT vt)) ())
        start (.success (.of (rollValtype (.VecT vt) x y))) start
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_valtype:clause:0» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.VecT vt)) start .unmatch start
        unfold SpecTec.«$subst_valtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:NumT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_valtype:clause:1» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.VecT vt))
          start (.success (.of (rollValtype (.VecT vt) x y))) start
        unfold SpecTec.«$subst_valtype:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:valtype:VecT»])
        · exact SpecTecExecution.Eval.pure (SpecTec.valtype.VecT vt)
  | RefT rt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_valtype_clauses» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.RefT rt)) ())
        start (.success (.of (rollValtype (.RefT rt) x y))) start
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_valtype:clause:0» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» (.RefT rt)) start .unmatch start
        unfold SpecTec.«$subst_valtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:NumT»])
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_valtype:clause:1» (Nat × Nat) (x, y)
              SpecTec.SpecTecCall.«$s_roll» (.RefT rt)) start .unmatch start
          unfold SpecTec.«$subst_valtype:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:valtype:VecT»])
        · apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_valtype:clause:2» (Nat × Nat) (x, y)
              SpecTec.SpecTecCall.«$s_roll» (.RefT rt))
            start (.success (.of (rollValtype (.RefT rt) x y))) start
          unfold SpecTec.«$subst_valtype:clause:2»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true
              (by simp [SpecTec.«exec:match:valtype:RefT»])
          · apply SpecTecExecution.Eval.bind_success
              (subst_reftype_roll_total rt x y start)
            exact SpecTecExecution.Eval.pure
              (SpecTec.valtype.RefT (rollReftype rt x y))
  | BotT =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_valtype_clauses» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» .BotT) ())
        start (.success (.of (rollValtype .BotT x y))) start
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_valtype:clause:0» (Nat × Nat) (x, y)
            SpecTec.SpecTecCall.«$s_roll» .BotT) start .unmatch start
        unfold SpecTec.«$subst_valtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:NumT»])
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_valtype:clause:1» (Nat × Nat) (x, y)
              SpecTec.SpecTecCall.«$s_roll» .BotT) start .unmatch start
          unfold SpecTec.«$subst_valtype:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:valtype:VecT»])
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_valtype:clause:2» (Nat × Nat) (x, y)
                SpecTec.SpecTecCall.«$s_roll» .BotT) start .unmatch start
            unfold SpecTec.«$subst_valtype:clause:2»
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:valtype:RefT»])
          · apply SpecTecExecution.firstSuccess_cons_success
            change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_valtype:clause:3» (Nat × Nat) (x, y)
                SpecTec.SpecTecCall.«$s_roll» .BotT)
              start (.success (.of (rollValtype .BotT x y))) start
            unfold SpecTec.«$subst_valtype:clause:3»
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · exact SpecTecExecution.Eval.pure SpecTec.valtype.BotT

theorem subst_valtype_roll_deterministic (t : SpecTec.valtype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.valtype,
        SpecTec.SpecTecCall.«$subst_valtype» (Nat × Nat) (x, y)
          SpecTec.SpecTecCall.«$s_roll» t⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollValtype t x y)) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_valtype_roll_total t x y start)

end properties.wasm_module_not_ok.Rejection
