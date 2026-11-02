import properties.wasm_module_ok.ConstSyntaxValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstGlobalGetValidation

theorem immutable_global_get_is_const
    (c : SpecTec.context) (x : SpecTec.globalidx)
    (t : SpecTec.valtype) (n : Nat)
    (hget : c.GLOBALS[x]? = some (.GlobalT .Cons t)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c
        (.«GLOBAL.GET» x)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$is_const_clauses» c (.«GLOBAL.GET» x)) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:0» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:1» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:2» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:3» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:4» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:5» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.I31»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:6» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:7» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:8» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW_FIXED»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:9» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:EXTERN.CONVERT»]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$is_const:clause:10» c (.«GLOBAL.GET» x))
    n (.success (.of true)) n
  unfold SpecTec.«$is_const:clause:10»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true
      (List.getElem?_eq_some_iff.mp hget).1
  rw [hget]
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure true

theorem other_global_get_is_not_const
    (c : SpecTec.context) (x : SpecTec.globalidx)
    (n : Nat)
    (hbad : ∀ t : SpecTec.valtype,
      c.GLOBALS[x]? ≠ some (.GlobalT .Cons t)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c
        (.«GLOBAL.GET» x)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$is_const_clauses» c (.«GLOBAL.GET» x)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:0» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:1» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:2» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:3» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:4» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:5» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.I31»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:6» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:7» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:8» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW_FIXED»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:9» c (.«GLOBAL.GET» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:EXTERN.CONVERT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:10» c (.«GLOBAL.GET» x))
      n .unmatch n
    unfold SpecTec.«$is_const:clause:10»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    cases hget : c.GLOBALS[x]? with
    | none =>
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (Nat.not_lt_of_ge (List.getElem?_eq_none_iff.mp hget))
    | some gt =>
        have hbound : x < c.GLOBALS.length :=
          (List.getElem?_eq_some_iff.mp hget).1
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hbound
        rw [hget]
        cases gt with
        | GlobalT m t =>
            cases m with
            | Cons => exact (hbad t hget).elim
            | Var =>
                apply SpecTecExecution.Eval.bind_unmatch
                exact SpecTecExecution.Eval.guard_false (by decide)
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$is_const:clause:11» c (.«GLOBAL.GET» x))
    n (.success (.of false)) n
  exact SpecTecExecution.Eval.pure false

theorem immutable_global_get_iff
    (c : SpecTec.context) (x : SpecTec.globalidx)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c
        (.«GLOBAL.GET» x)⟩)
      n (.success (.of true)) finalSupply ↔
      (∃ t : SpecTec.valtype,
        c.GLOBALS[x]? = some (.GlobalT .Cons t)) ∧
        finalSupply = n := by
  constructor
  · intro hcall
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request a b hp
      cases hp
    by_cases himmutable : ∃ t : SpecTec.valtype,
        c.GLOBALS[x]? = some (.GlobalT .Cons t)
    · obtain ⟨t, hget⟩ := himmutable
      have hknown := immutable_global_get_is_const c x t n hget
      obtain ⟨_, hsupply⟩ :=
        SpecTecExecution.eval_deterministic hdet hcall hknown
      exact ⟨⟨t, hget⟩, hsupply⟩
    · have hbad : ∀ t : SpecTec.valtype,
          c.GLOBALS[x]? ≠ some (.GlobalT .Cons t) := by
        intro t hget
        exact himmutable ⟨t, hget⟩
      have hfalse := other_global_get_is_not_const c x n hbad
      obtain ⟨heq, _⟩ :=
        SpecTecExecution.eval_deterministic hdet hcall hfalse
      cases heq
  · rintro ⟨⟨t, hget⟩, rfl⟩
    exact immutable_global_get_is_const c x t finalSupply hget

theorem const_ok_global_get_immutable
    (c : SpecTec.context) (target : SpecTec.valtype)
    (xs : SpecTec.const) (x : SpecTec.globalidx)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c target xs⟩)
      n (.success (.of ())) finalSupply)
    (hmem : SpecTec.instr.«GLOBAL.GET» x ∈ xs) :
    ∃ t : SpecTec.valtype,
      c.GLOBALS[x]? = some (.GlobalT .Cons t) := by
  obtain ⟨start, finish, his⟩ :=
    ConstSyntaxValidation.const_ok_member_is_const
      c target xs n finalSupply hcall (.«GLOBAL.GET» x) hmem
  exact ((immutable_global_get_iff c x start finish).1 his).1

end properties.wasm_module_ok.ConstGlobalGetValidation

