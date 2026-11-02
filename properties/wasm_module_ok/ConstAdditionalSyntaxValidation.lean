import properties.wasm_module_ok.ConstRefSyntaxValidation
import properties.wasm_module_ok.ConstGlobalGetValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstAdditionalSyntaxValidation

theorem vec_const_is_const
    (c : SpecTec.context) (v : SpecTec.vec_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c
        (.«VEC.CONST» v)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$is_const_clauses» c (.«VEC.CONST» v)))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:0» c (.«VEC.CONST» v)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:1» c (.«VEC.CONST» v)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$is_const:clause:2» c (.«VEC.CONST» v))
    n (.success (.of true)) n
  unfold SpecTec.«$is_const:clause:2»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure true

theorem ref_i31_is_const
    (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c
        .«REF.I31»⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$is_const_clauses» c .«REF.I31»))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:0» c .«REF.I31») n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:1» c .«REF.I31») n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:2» c .«REF.I31») n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:3» c .«REF.I31») n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:4» c .«REF.I31») n .unmatch n
    unfold SpecTec.«$is_const:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$is_const:clause:5» c .«REF.I31»)
    n (.success (.of true)) n
  unfold SpecTec.«$is_const:clause:5»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure true

theorem struct_new_is_const
    (c : SpecTec.context) (ti : SpecTec.typeidx) (op : SpecTec.initop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c
        (.«STRUCT.NEW» ti op)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$is_const_clauses» c (.«STRUCT.NEW» ti op)))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:0» c (.«STRUCT.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:1» c (.«STRUCT.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:2» c (.«STRUCT.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:3» c (.«STRUCT.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:4» c (.«STRUCT.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:5» c (.«STRUCT.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.I31»]))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$is_const:clause:6» c (.«STRUCT.NEW» ti op))
    n (.success (.of true)) n
  unfold SpecTec.«$is_const:clause:6»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure true

theorem array_new_is_const
    (c : SpecTec.context) (ti : SpecTec.typeidx) (op : SpecTec.initop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c
        (.«ARRAY.NEW» ti op)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$is_const_clauses» c (.«ARRAY.NEW» ti op)))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:0» c (.«ARRAY.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:1» c (.«ARRAY.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:2» c (.«ARRAY.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:3» c (.«ARRAY.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:4» c (.«ARRAY.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:5» c (.«ARRAY.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.I31»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:6» c (.«ARRAY.NEW» ti op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$is_const:clause:7» c (.«ARRAY.NEW» ti op))
    n (.success (.of true)) n
  unfold SpecTec.«$is_const:clause:7»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure true

theorem array_new_fixed_is_const
    (c : SpecTec.context) (ti : SpecTec.typeidx) (len : SpecTec.u32) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c
        (.«ARRAY.NEW_FIXED» ti len)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$is_const_clauses» c (.«ARRAY.NEW_FIXED» ti len)))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:0» c (.«ARRAY.NEW_FIXED» ti len)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:1» c (.«ARRAY.NEW_FIXED» ti len)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:2» c (.«ARRAY.NEW_FIXED» ti len)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:3» c (.«ARRAY.NEW_FIXED» ti len)) n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:4» c (.«ARRAY.NEW_FIXED» ti len)) n .unmatch n
    unfold SpecTec.«$is_const:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:5» c (.«ARRAY.NEW_FIXED» ti len)) n .unmatch n
    unfold SpecTec.«$is_const:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.I31»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:6» c (.«ARRAY.NEW_FIXED» ti len)) n .unmatch n
    unfold SpecTec.«$is_const:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:7» c (.«ARRAY.NEW_FIXED» ti len)) n .unmatch n
    unfold SpecTec.«$is_const:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$is_const:clause:8» c (.«ARRAY.NEW_FIXED» ti len))
    n (.success (.of true)) n
  unfold SpecTec.«$is_const:clause:8»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure true

theorem extern_convert_is_const
    (c : SpecTec.context) (op : SpecTec.externop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c
        (.«EXTERN.CONVERT» op)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$is_const_clauses» c (.«EXTERN.CONVERT» op)))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:0» c (.«EXTERN.CONVERT» op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:1» c (.«EXTERN.CONVERT» op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:2» c (.«EXTERN.CONVERT» op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:3» c (.«EXTERN.CONVERT» op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:4» c (.«EXTERN.CONVERT» op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:5» c (.«EXTERN.CONVERT» op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.I31»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:6» c (.«EXTERN.CONVERT» op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:7» c (.«EXTERN.CONVERT» op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:8» c (.«EXTERN.CONVERT» op)) n .unmatch n
    unfold SpecTec.«$is_const:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:ARRAY.NEW_FIXED»]))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$is_const:clause:9» c (.«EXTERN.CONVERT» op))
    n (.success (.of true)) n
  unfold SpecTec.«$is_const:clause:9»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure true

inductive Syntax (c : SpecTec.context) : SpecTec.instr → Prop where
  | arithmetic (i : SpecTec.instr)
      (h : i ∈ ConstArithmeticValidation.arithmeticOps) : Syntax c i
  | num (v : SpecTec.num_) : Syntax c (.CONST v)
  | vec (v : SpecTec.vec_) : Syntax c (.«VEC.CONST» v)
  | refNull (ht : SpecTec.heaptype) : Syntax c (.«REF.NULL» ht)
  | refFunc (x : SpecTec.funcidx) : Syntax c (.«REF.FUNC» x)
  | refI31 : Syntax c .«REF.I31»
  | structNew (ti : SpecTec.typeidx) (op : SpecTec.initop_) :
      Syntax c (.«STRUCT.NEW» ti op)
  | arrayNew (ti : SpecTec.typeidx) (op : SpecTec.initop_) :
      Syntax c (.«ARRAY.NEW» ti op)
  | arrayNewFixed (ti : SpecTec.typeidx) (len : SpecTec.u32) :
      Syntax c (.«ARRAY.NEW_FIXED» ti len)
  | externConvert (op : SpecTec.externop_) :
      Syntax c (.«EXTERN.CONVERT» op)
  | globalGet (x : SpecTec.globalidx) (t : SpecTec.valtype)
      (h : c.GLOBALS[x]? = some (.GlobalT .Cons t)) :
      Syntax c (.«GLOBAL.GET» x)

theorem syntax_is_const
    (c : SpecTec.context) (i : SpecTec.instr) (n : Nat)
    (h : Syntax c i) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
      n (.success (.of true)) n := by
  cases h with
  | arithmetic i hi =>
      exact ConstArithmeticValidation.arithmetic_is_const c i n hi
  | num v => exact ConstArithmeticValidation.const_literal_is_const c v n
  | vec v => exact vec_const_is_const c v n
  | refNull ht => exact ConstRefSyntaxValidation.ref_null_is_const c ht n
  | refFunc x => exact ConstRefSyntaxValidation.ref_func_is_const c x n
  | refI31 => exact ref_i31_is_const c n
  | structNew ti op => exact struct_new_is_const c ti op n
  | arrayNew ti op => exact array_new_is_const c ti op n
  | arrayNewFixed ti len => exact array_new_fixed_is_const c ti len n
  | externConvert op => exact extern_convert_is_const c op n
  | globalGet x t hget =>
      exact ConstGlobalGetValidation.immutable_global_get_is_const
        c x t n hget

theorem syntax_iter_total
    (c : SpecTec.context) (xs : List SpecTec.instr) (n : Nat)
    (hall : ∀ i ∈ xs, Syntax c i) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Const_ok:rule:iter:0»
        c xs⟩)
      n (.success (.of ())) n := by
  induction xs with
  | nil => exact ConstArithmeticValidation.const_iter_nil_total c n
  | cons i rest ih =>
      apply (ConstSyntaxValidation.const_iter_cons_success_iff
        c i rest n n).2
      exact ⟨n, syntax_is_const c i n (hall i (by simp)),
        ih (fun j hj => hall j (by simp [hj]))⟩

end properties.wasm_module_ok.ConstAdditionalSyntaxValidation
