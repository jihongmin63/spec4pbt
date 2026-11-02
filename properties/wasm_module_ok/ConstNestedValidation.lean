import properties.wasm_module_ok.ConstSyntaxValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstNestedValidation

theorem is_const_block_false
    (c : SpecTec.context) (bt : SpecTec.blocktype) (body : List SpecTec.instr) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c (.BLOCK bt body)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$is_const_clauses» c (.BLOCK bt body)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:0» c (.BLOCK bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:1» c (.BLOCK bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:2» c (.BLOCK bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:3» c (.BLOCK bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:4» c (.BLOCK bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:5» c (.BLOCK bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.I31»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:6» c (.BLOCK bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:7» c (.BLOCK bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:8» c (.BLOCK bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW_FIXED»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:9» c (.BLOCK bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:EXTERN.CONVERT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:10» c (.BLOCK bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.GET»]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$is_const:clause:11» c (.BLOCK bt body)) n (.success (.of false)) n
  exact SpecTecExecution.Eval.pure false

theorem is_const_loop_false
    (c : SpecTec.context) (bt : SpecTec.blocktype) (body : List SpecTec.instr) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c (.LOOP bt body)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$is_const_clauses» c (.LOOP bt body)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:0» c (.LOOP bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:1» c (.LOOP bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:2» c (.LOOP bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:3» c (.LOOP bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:4» c (.LOOP bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:5» c (.LOOP bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.I31»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:6» c (.LOOP bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:7» c (.LOOP bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:8» c (.LOOP bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW_FIXED»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:9» c (.LOOP bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:EXTERN.CONVERT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:10» c (.LOOP bt body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.GET»]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$is_const:clause:11» c (.LOOP bt body)) n (.success (.of false)) n
  exact SpecTecExecution.Eval.pure false

theorem is_const_if_false
    (c : SpecTec.context) (bt : SpecTec.blocktype) (yes no : List SpecTec.instr) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c (.«IF % % ELSE %» bt yes no)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$is_const_clauses» c (.«IF % % ELSE %» bt yes no)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:0» c (.«IF % % ELSE %» bt yes no)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:1» c (.«IF % % ELSE %» bt yes no)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:2» c (.«IF % % ELSE %» bt yes no)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:3» c (.«IF % % ELSE %» bt yes no)) n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:4» c (.«IF % % ELSE %» bt yes no)) n .unmatch n
    unfold SpecTec.«$is_const:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:5» c (.«IF % % ELSE %» bt yes no)) n .unmatch n
    unfold SpecTec.«$is_const:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.I31»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:6» c (.«IF % % ELSE %» bt yes no)) n .unmatch n
    unfold SpecTec.«$is_const:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:7» c (.«IF % % ELSE %» bt yes no)) n .unmatch n
    unfold SpecTec.«$is_const:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:8» c (.«IF % % ELSE %» bt yes no)) n .unmatch n
    unfold SpecTec.«$is_const:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW_FIXED»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:9» c (.«IF % % ELSE %» bt yes no)) n .unmatch n
    unfold SpecTec.«$is_const:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:EXTERN.CONVERT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:10» c (.«IF % % ELSE %» bt yes no)) n .unmatch n
    unfold SpecTec.«$is_const:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.GET»]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$is_const:clause:11» c (.«IF % % ELSE %» bt yes no)) n (.success (.of false)) n
  exact SpecTecExecution.Eval.pure false

theorem is_const_tryTable_false
    (c : SpecTec.context) (bt : SpecTec.blocktype) (catches : List SpecTec.«catch») (body : List SpecTec.instr) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c (.TRY_TABLE bt catches body)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$is_const_clauses» c (.TRY_TABLE bt catches body)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:0» c (.TRY_TABLE bt catches body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:1» c (.TRY_TABLE bt catches body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:2» c (.TRY_TABLE bt catches body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:3» c (.TRY_TABLE bt catches body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:4» c (.TRY_TABLE bt catches body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:4»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.FUNC»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:5» c (.TRY_TABLE bt catches body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:5»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:REF.I31»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:6» c (.TRY_TABLE bt catches body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:6»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:STRUCT.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:7» c (.TRY_TABLE bt catches body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:7»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:8» c (.TRY_TABLE bt catches body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:8»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:ARRAY.NEW_FIXED»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:9» c (.TRY_TABLE bt catches body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:9»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:EXTERN.CONVERT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$is_const:clause:10» c (.TRY_TABLE bt catches body)) n .unmatch n
    unfold SpecTec.«$is_const:clause:10»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:instr:GLOBAL.GET»]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$is_const:clause:11» c (.TRY_TABLE bt catches body)) n (.success (.of false)) n
  exact SpecTecExecution.Eval.pure false

inductive Nested : SpecTec.instr → Prop where
  | block (bt : SpecTec.blocktype) (body : List SpecTec.instr) :
      Nested (.BLOCK bt body)
  | loop (bt : SpecTec.blocktype) (body : List SpecTec.instr) :
      Nested (.LOOP bt body)
  | if_ (bt : SpecTec.blocktype) (yes no : List SpecTec.instr) :
      Nested (.«IF % % ELSE %» bt yes no)
  | tryTable (bt : SpecTec.blocktype) (catches : List SpecTec.«catch»)
      (body : List SpecTec.instr) : Nested (.TRY_TABLE bt catches body)

theorem is_const_true_not_nested
    (c : SpecTec.context) (i : SpecTec.instr)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c i⟩)
      start (.success (.of true)) finish) : ¬ Nested i := by
  intro hnested
  cases hnested with
  | block bt body =>
      have hfalse := is_const_block_false c bt body start
      cases (SpecTecExecution.eval_deterministic
        properties.wasm_module_not_ok.Rejection.program_primitive_deterministic
        hfalse hcall).1
  | loop bt body =>
      have hfalse := is_const_loop_false c bt body start
      cases (SpecTecExecution.eval_deterministic
        properties.wasm_module_not_ok.Rejection.program_primitive_deterministic
        hfalse hcall).1
  | if_ bt yes no =>
      have hfalse := is_const_if_false c bt yes no start
      cases (SpecTecExecution.eval_deterministic
        properties.wasm_module_not_ok.Rejection.program_primitive_deterministic
        hfalse hcall).1
  | tryTable bt catches body =>
      have hfalse := is_const_tryTable_false c bt catches body start
      cases (SpecTecExecution.eval_deterministic
        properties.wasm_module_not_ok.Rejection.program_primitive_deterministic
        hfalse hcall).1

theorem const_ok_no_nested
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      n (.success (.of ())) finalSupply)
    (i : SpecTec.instr) (hmem : i ∈ xs) : ¬ Nested i := by
  obtain ⟨start, finish, his⟩ :=
    ConstSyntaxValidation.const_ok_member_is_const c t xs n finalSupply
      hcall i hmem
  exact is_const_true_not_nested c i start finish his

inductive RefOccurs : SpecTec.instr → SpecTec.funcidx → Prop where
  | direct (x : SpecTec.funcidx) : RefOccurs (.«REF.FUNC» x) x
  | block (bt : SpecTec.blocktype) (body : List SpecTec.instr)
      (i : SpecTec.instr) (x : SpecTec.funcidx)
      (hmem : i ∈ body) (hocc : RefOccurs i x) :
      RefOccurs (.BLOCK bt body) x
  | loop (bt : SpecTec.blocktype) (body : List SpecTec.instr)
      (i : SpecTec.instr) (x : SpecTec.funcidx)
      (hmem : i ∈ body) (hocc : RefOccurs i x) :
      RefOccurs (.LOOP bt body) x
  | ifYes (bt : SpecTec.blocktype) (yes no : List SpecTec.instr)
      (i : SpecTec.instr) (x : SpecTec.funcidx)
      (hmem : i ∈ yes) (hocc : RefOccurs i x) :
      RefOccurs (.«IF % % ELSE %» bt yes no) x
  | ifNo (bt : SpecTec.blocktype) (yes no : List SpecTec.instr)
      (i : SpecTec.instr) (x : SpecTec.funcidx)
      (hmem : i ∈ no) (hocc : RefOccurs i x) :
      RefOccurs (.«IF % % ELSE %» bt yes no) x
  | tryTable (bt : SpecTec.blocktype) (catches : List SpecTec.«catch»)
      (body : List SpecTec.instr) (i : SpecTec.instr)
      (x : SpecTec.funcidx) (hmem : i ∈ body) (hocc : RefOccurs i x) :
      RefOccurs (.TRY_TABLE bt catches body) x

theorem const_ok_ref_occurs_direct
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      n (.success (.of ())) finalSupply)
    (i : SpecTec.instr) (x : SpecTec.funcidx)
    (hmem : i ∈ xs) (hocc : RefOccurs i x) :
    SpecTec.instr.«REF.FUNC» x ∈ xs := by
  cases hocc with
  | direct x => exact hmem
  | block bt body j x _ _ =>
      exact ((const_ok_no_nested c t xs n finalSupply hcall _ hmem)
        (.block bt body)).elim
  | loop bt body j x _ _ =>
      exact ((const_ok_no_nested c t xs n finalSupply hcall _ hmem)
        (.loop bt body)).elim
  | ifYes bt yes no j x _ _ =>
      exact ((const_ok_no_nested c t xs n finalSupply hcall _ hmem)
        (.if_ bt yes no)).elim
  | ifNo bt yes no j x _ _ =>
      exact ((const_ok_no_nested c t xs n finalSupply hcall _ hmem)
        (.if_ bt yes no)).elim
  | tryTable bt catches body j x _ _ =>
      exact ((const_ok_no_nested c t xs n finalSupply hcall _ hmem)
        (.tryTable bt catches body)).elim

end properties.wasm_module_ok.ConstNestedValidation
