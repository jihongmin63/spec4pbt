import properties.wasm_module_ok.ConstArithmeticValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstRefSyntaxValidation

theorem ref_null_is_const
    (c : SpecTec.context) (ht : SpecTec.heaptype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c
        (.«REF.NULL» ht)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$is_const_clauses» c (.«REF.NULL» ht)))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:0» c (.«REF.NULL» ht)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:1» c (.«REF.NULL» ht)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:2» c (.«REF.NULL» ht)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$is_const:clause:3» c (.«REF.NULL» ht))
    n (.success (.of true)) n
  unfold SpecTec.«$is_const:clause:3»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure true

theorem ref_func_is_const
    (c : SpecTec.context) (x : SpecTec.funcidx) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c
        (.«REF.FUNC» x)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$is_const_clauses» c (.«REF.FUNC» x)))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:0» c (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:1» c (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:2» c (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:VEC.CONST»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:3» c (.«REF.FUNC» x)) n .unmatch n
    unfold SpecTec.«$is_const:clause:3»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:instr:REF.NULL»]))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$is_const:clause:4» c (.«REF.FUNC» x))
    n (.success (.of true)) n
  unfold SpecTec.«$is_const:clause:4»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure true

def basicConstSyntax (i : SpecTec.instr) : Prop :=
  ConstArithmeticValidation.simpleConstSyntax i ∨
    (∃ ht, i = .«REF.NULL» ht) ∨
    (∃ x, i = .«REF.FUNC» x)

theorem basic_const_iter_total
    (c : SpecTec.context) (xs : List SpecTec.instr) (n : Nat)
    (hall : ∀ i ∈ xs, basicConstSyntax i) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Const_ok:rule:iter:0»
        c xs⟩)
      n (.success (.of ())) n := by
  induction xs with
  | nil => exact ConstArithmeticValidation.const_iter_nil_total c n
  | cons i rest ih =>
      apply (ConstSyntaxValidation.const_iter_cons_success_iff
        c i rest n n).2
      have hhead := hall i (by simp)
      have his : SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
          n (.success (.of true)) n := by
        rcases hhead with hsimple | ⟨ht, rfl⟩ | ⟨x, rfl⟩
        · rcases hsimple with harith | ⟨v, rfl⟩
          · exact ConstArithmeticValidation.arithmetic_is_const
              c i n harith
          · exact ConstArithmeticValidation.const_literal_is_const c v n
        · exact ref_null_is_const c ht n
        · exact ref_func_is_const c x n
      exact ⟨n, his, ih (fun j hj => hall j (by simp [hj]))⟩

end properties.wasm_module_ok.ConstRefSyntaxValidation
