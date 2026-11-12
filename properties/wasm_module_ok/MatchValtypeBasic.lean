import properties.wasm_module_ok.MatchNullValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchValtypeBasic

theorem match_valtype_num_total
    (dts : List SpecTec.deftype) (a b : SpecTec.numtype)
    (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.NumT a) (.NumT b)⟩)
      start (.success (.of (decide (b = a)))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_valtype_clauses» dts (.NumT a) (.NumT b)))
    start (.success (.of (decide (b = a)))) start
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$match_valtype:clause:0» dts (.NumT a) (.NumT b))
    start (.success (.of (decide (b = a)))) start
  unfold SpecTec.«$match_valtype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
      · exact MatchPrimitiveValidation.match_numtype_total dts a b start
      · exact SpecTecExecution.Eval.pure (decide (b = a))

theorem match_valtype_vec_total
    (dts : List SpecTec.deftype) (a b : SpecTec.vectype)
    (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.VecT a) (.VecT b)⟩)
      start (.success (.of (decide (a = b)))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_valtype_clauses» dts (.VecT a) (.VecT b)))
    start (.success (.of (decide (a = b)))) start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_valtype:clause:0» dts (.VecT a) (.VecT b))
      start .unmatch start
    unfold SpecTec.«$match_valtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:valtype:NumT»]))
  · apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_valtype:clause:1» dts (.VecT a) (.VecT b))
      start (.success (.of (decide (a = b)))) start
    unfold SpecTec.«$match_valtype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact MatchPrimitiveValidation.match_vectype_total dts a b start
        · exact SpecTecExecution.Eval.pure (decide (a = b))

theorem match_valtype_bot_total
    (dts : List SpecTec.deftype) (t : SpecTec.valtype)
    (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts .BotT t⟩)
      start (.success (.of true)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_valtype_clauses» dts .BotT t))
    start (.success (.of true)) start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_valtype:clause:0» dts .BotT t) start .unmatch start
    unfold SpecTec.«$match_valtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:valtype:NumT»]))
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_valtype:clause:1» dts .BotT t) start .unmatch start
      unfold SpecTec.«$match_valtype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:VecT»]))
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_valtype:clause:2» dts .BotT t) start .unmatch start
        unfold SpecTec.«$match_valtype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:valtype:RefT»]))
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_valtype:clause:3» dts .BotT t)
          start (.success (.of true)) start
        unfold SpecTec.«$match_valtype:clause:3»
        exact SpecTecExecution.Eval.bind_success
          (SpecTecExecution.Eval.guard_true rfl)
          (SpecTecExecution.Eval.pure true)

theorem match_valtype_num_other_total
    (dts : List SpecTec.deftype) (a : SpecTec.numtype)
    (t : SpecTec.valtype) (start : Nat)
    (h : SpecTec.«exec:match:valtype:NumT» t = false) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.NumT a) t⟩)
      start (.success (.of false)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_valtype_clauses» dts (.NumT a) t))
    start (.success (.of false)) start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_valtype:clause:0» dts (.NumT a) t)
      start .unmatch start
    unfold SpecTec.«$match_valtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [h]))
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_valtype:clause:1» dts (.NumT a) t)
        start .unmatch start
      unfold SpecTec.«$match_valtype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:VecT»]))
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_valtype:clause:2» dts (.NumT a) t)
          start .unmatch start
        unfold SpecTec.«$match_valtype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:valtype:RefT»]))
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$match_valtype:clause:3» dts (.NumT a) t)
            start .unmatch start
          unfold SpecTec.«$match_valtype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:valtype:BotT»]))
        · apply SpecTecExecution.tryClauses_cons_success
          exact SpecTecExecution.Eval.pure false

theorem match_valtype_num_vec_total
    (dts : List SpecTec.deftype) (a : SpecTec.numtype)
    (b : SpecTec.vectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.NumT a) (.VecT b)⟩)
      start (.success (.of false)) start := by
  exact match_valtype_num_other_total dts a (.VecT b) start
    (by simp [SpecTec.«exec:match:valtype:NumT»])

theorem match_valtype_num_ref_total
    (dts : List SpecTec.deftype) (a : SpecTec.numtype)
    (b : SpecTec.reftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.NumT a) (.RefT b)⟩)
      start (.success (.of false)) start := by
  exact match_valtype_num_other_total dts a (.RefT b) start
    (by simp [SpecTec.«exec:match:valtype:NumT»])

theorem match_valtype_num_bot_total
    (dts : List SpecTec.deftype) (a : SpecTec.numtype)
    (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.NumT a) .BotT⟩)
      start (.success (.of false)) start := by
  exact match_valtype_num_other_total dts a .BotT start
    (by simp [SpecTec.«exec:match:valtype:NumT»])

theorem match_valtype_vec_other_total
    (dts : List SpecTec.deftype) (a : SpecTec.vectype)
    (t : SpecTec.valtype) (start : Nat)
    (h : SpecTec.«exec:match:valtype:VecT» t = false) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.VecT a) t⟩)
      start (.success (.of false)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_valtype_clauses» dts (.VecT a) t))
    start (.success (.of false)) start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_valtype:clause:0» dts (.VecT a) t)
      start .unmatch start
    unfold SpecTec.«$match_valtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:valtype:NumT»]))
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_valtype:clause:1» dts (.VecT a) t)
        start .unmatch start
      unfold SpecTec.«$match_valtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp [h]))
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_valtype:clause:2» dts (.VecT a) t)
          start .unmatch start
        unfold SpecTec.«$match_valtype:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:valtype:RefT»]))
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$match_valtype:clause:3» dts (.VecT a) t)
            start .unmatch start
          unfold SpecTec.«$match_valtype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:valtype:BotT»]))
        · apply SpecTecExecution.tryClauses_cons_success
          exact SpecTecExecution.Eval.pure false

theorem match_valtype_vec_num_total
    (dts : List SpecTec.deftype) (a : SpecTec.vectype)
    (b : SpecTec.numtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.VecT a) (.NumT b)⟩)
      start (.success (.of false)) start := by
  exact match_valtype_vec_other_total dts a (.NumT b) start
    (by simp [SpecTec.«exec:match:valtype:VecT»])

theorem match_valtype_vec_ref_total
    (dts : List SpecTec.deftype) (a : SpecTec.vectype)
    (b : SpecTec.reftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.VecT a) (.RefT b)⟩)
      start (.success (.of false)) start := by
  exact match_valtype_vec_other_total dts a (.RefT b) start
    (by simp [SpecTec.«exec:match:valtype:VecT»])

theorem match_valtype_vec_bot_total
    (dts : List SpecTec.deftype) (a : SpecTec.vectype)
    (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.VecT a) .BotT⟩)
      start (.success (.of false)) start := by
  exact match_valtype_vec_other_total dts a .BotT start
    (by simp [SpecTec.«exec:match:valtype:VecT»])

theorem match_valtype_ref_other_total
    (dts : List SpecTec.deftype) (a : SpecTec.reftype)
    (t : SpecTec.valtype) (start : Nat)
    (h : SpecTec.«exec:match:valtype:RefT» t = false) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.RefT a) t⟩)
      start (.success (.of false)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_valtype_clauses» dts (.RefT a) t))
    start (.success (.of false)) start
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_valtype:clause:0» dts (.RefT a) t)
      start .unmatch start
    unfold SpecTec.«$match_valtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:valtype:NumT»]))
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_valtype:clause:1» dts (.RefT a) t)
        start .unmatch start
      unfold SpecTec.«$match_valtype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:VecT»]))
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_valtype:clause:2» dts (.RefT a) t)
          start .unmatch start
        unfold SpecTec.«$match_valtype:clause:2»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by simp [h]))
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$match_valtype:clause:3» dts (.RefT a) t)
            start .unmatch start
          unfold SpecTec.«$match_valtype:clause:3»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:valtype:BotT»]))
        · apply SpecTecExecution.tryClauses_cons_success
          exact SpecTecExecution.Eval.pure false

theorem match_valtype_ref_num_total
    (dts : List SpecTec.deftype) (a : SpecTec.reftype)
    (b : SpecTec.numtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.RefT a) (.NumT b)⟩)
      start (.success (.of false)) start := by
  exact match_valtype_ref_other_total dts a (.NumT b) start
    (by simp [SpecTec.«exec:match:valtype:RefT»])

theorem match_valtype_ref_vec_total
    (dts : List SpecTec.deftype) (a : SpecTec.reftype)
    (b : SpecTec.vectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.RefT a) (.VecT b)⟩)
      start (.success (.of false)) start := by
  exact match_valtype_ref_other_total dts a (.VecT b) start
    (by simp [SpecTec.«exec:match:valtype:RefT»])

theorem match_valtype_ref_bot_total
    (dts : List SpecTec.deftype) (a : SpecTec.reftype)
    (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_valtype» dts (.RefT a) .BotT⟩)
      start (.success (.of false)) start := by
  exact match_valtype_ref_other_total dts a .BotT start
    (by simp [SpecTec.«exec:match:valtype:RefT»])

end properties.wasm_module_ok.MatchValtypeBasic
