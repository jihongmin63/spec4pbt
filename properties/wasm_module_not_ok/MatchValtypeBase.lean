import properties.wasm_module_not_ok.MatchValtypeTrace

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_valtype_num_total (d : List SpecTec.deftype)
    (a b : SpecTec.numtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» d
        (.NumT a) (.NumT b)⟩)
      start (.success (.of (decide (a = b)))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_valtype_clauses» d (.NumT a) (.NumT b)) ())
    start (.success (.of (decide (a = b)))) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_valtype:clause:0» d (.NumT a) (.NumT b))
    start (.success (.of (decide (a = b)))) start
  unfold SpecTec.«$match_valtype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true
      (by simp [SpecTec.«exec:match:valtype:NumT»])
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:valtype:NumT»])
    · apply SpecTecExecution.Eval.bind_success
        (match_numtype_total d a b start)
      exact SpecTecExecution.Eval.pure (decide (a = b))

theorem match_valtype_vec_total (d : List SpecTec.deftype)
    (a b : SpecTec.vectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» d
        (.VecT a) (.VecT b)⟩)
      start (.success (.of (decide (a = b)))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_valtype_clauses» d (.VecT a) (.VecT b)) ())
    start (.success (.of (decide (a = b)))) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_valtype:clause:0» d (.VecT a) (.VecT b))
      start .unmatch start
    unfold SpecTec.«$match_valtype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:valtype:NumT»])
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_valtype:clause:1» d (.VecT a) (.VecT b))
      start (.success (.of (decide (a = b)))) start
    unfold SpecTec.«$match_valtype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:valtype:VecT»])
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:valtype:VecT»])
      · apply SpecTecExecution.Eval.bind_success
          (match_vectype_total d a b start)
        exact SpecTecExecution.Eval.pure (decide (a = b))

theorem match_valtype_bot_total (d : List SpecTec.deftype)
    (b : SpecTec.valtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» d
        .BotT b⟩)
      start (.success (.of true)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_valtype_clauses» d .BotT b) ())
    start (.success (.of true)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_valtype:clause:0» d .BotT b)
      start .unmatch start
    unfold SpecTec.«$match_valtype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by decide)
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_valtype:clause:1» d .BotT b)
        start .unmatch start
      unfold SpecTec.«$match_valtype:clause:1»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false (by decide)
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_valtype:clause:2» d .BotT b)
          start .unmatch start
        unfold SpecTec.«$match_valtype:clause:2»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false (by decide)
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_valtype:clause:3» d .BotT b)
          start (.success (.of true)) start
        unfold SpecTec.«$match_valtype:clause:3»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true (by decide)
        · exact SpecTecExecution.Eval.pure true

theorem match_valtype_num_deterministic (d : List SpecTec.deftype)
    (a b : SpecTec.numtype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» d
        (.NumT a) (.NumT b)⟩)
      start outcome finalSupply) :
    outcome = .success (.of (decide (a = b))) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_valtype_num_total d a b start)

theorem match_valtype_vec_deterministic (d : List SpecTec.deftype)
    (a b : SpecTec.vectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» d
        (.VecT a) (.VecT b)⟩)
      start outcome finalSupply) :
    outcome = .success (.of (decide (a = b))) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_valtype_vec_total d a b start)

theorem match_valtype_bot_deterministic (d : List SpecTec.deftype)
    (b : SpecTec.valtype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» d .BotT b⟩)
      start outcome finalSupply) :
    outcome = .success (.of true) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_valtype_bot_total d b start)

end properties.wasm_module_not_ok.Rejection
