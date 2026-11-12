import properties.wasm_module_ok.ConstSyntaxValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArithmeticValidation

def arithmeticOps : List SpecTec.instr :=
  [.BINOP (.I32 .IAdd), .BINOP (.I32 .ISub),
   .BINOP (.I32 .IMul), .BINOP (.I64 .IAdd),
   .BINOP (.I64 .ISub), .BINOP (.I64 .IMul)]

theorem arithmetic_is_const
    (c : SpecTec.context) (i : SpecTec.instr)
    (n : Nat) (h : i ∈ arithmeticOps) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$is_const_clauses» c i))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$is_const:clause:0» c i)
    n (.success (.of true)) n
  unfold SpecTec.«$is_const:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true
      (by simpa [arithmeticOps] using h)
  · exact SpecTecExecution.Eval.pure true

theorem i32_add_is_const
    (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$is_const» c
          (.BINOP (.I32 .IAdd))⟩)
      n (.success (.of true)) n :=
  arithmetic_is_const c _ n (by simp [arithmeticOps])

theorem const_literal_is_const
    (c : SpecTec.context) (v : SpecTec.num_)
    (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c
        (.CONST v)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$is_const_clauses» c (.CONST v)))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$is_const:clause:0» c (.CONST v))
      n .unmatch n
    unfold SpecTec.«$is_const:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$is_const:clause:1» c (.CONST v))
    n (.success (.of true)) n
  unfold SpecTec.«$is_const:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure true

theorem const_iter_nil_total
    (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Const_ok:rule:iter:0»
        c []⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«Const_ok:rule:iter:0_clauses» c []))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Const_ok:rule:iter:0:clause:0» c [])
    n (.success (.of ())) n
  unfold SpecTec.«Const_ok:rule:iter:0:clause:0»
  exact SpecTecExecution.Eval.pure ()

theorem arithmetic_iter_total
    (c : SpecTec.context) (xs : List SpecTec.instr)
    (n : Nat) (hall : ∀ i ∈ xs, i ∈ arithmeticOps) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Const_ok:rule:iter:0»
        c xs⟩)
      n (.success (.of ())) n := by
  induction xs with
  | nil => exact const_iter_nil_total c n
  | cons i rest ih =>
      apply (ConstSyntaxValidation.const_iter_cons_success_iff
        c i rest n n).2
      exact ⟨n, arithmetic_is_const c i n
        (hall i (by simp)), ih (fun j hj =>
          hall j (by simp [hj]))⟩

def simpleConstSyntax (i : SpecTec.instr) : Prop :=
  i ∈ arithmeticOps ∨ ∃ v : SpecTec.num_, i = .CONST v

theorem simple_const_iter_total
    (c : SpecTec.context) (xs : List SpecTec.instr)
    (n : Nat) (hall : ∀ i ∈ xs, simpleConstSyntax i) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Const_ok:rule:iter:0»
        c xs⟩)
      n (.success (.of ())) n := by
  induction xs with
  | nil => exact const_iter_nil_total c n
  | cons i rest ih =>
      apply (ConstSyntaxValidation.const_iter_cons_success_iff
        c i rest n n).2
      have hhead := hall i (by simp)
      have his : SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
          n (.success (.of true)) n := by
        rcases hhead with harith | ⟨v, rfl⟩
        · exact arithmetic_is_const c i n harith
        · exact const_literal_is_const c v n
      exact ⟨n, his, ih (fun j hj =>
        hall j (by simp [hj]))⟩

end properties.wasm_module_ok.ConstArithmeticValidation
