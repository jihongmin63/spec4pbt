import properties.wasm_module_ok.ConstStepTrace
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstLiteralEffect

def numericType : SpecTec.num_ → SpecTec.numtype
  | .I32 _ => .I32T
  | .I64 _ => .I64T
  | .F32 _ => .F32T
  | .F64 _ => .F64T

theorem numeric_type_call (v : SpecTec.num_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.numtype,
        SpecTec.Call.«$type_num»
          SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 v⟩)
      n (.success (.of (numericType v))) n := by
  cases v with
  | I32 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$type_num_clauses»
            SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.I32 a)))
        n (.success (.of SpecTec.numtype.I32T)) n
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_num:clause:0»
          SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.I32 a))
        n (.success (.of SpecTec.numtype.I32T)) n
      unfold SpecTec.«$type_num:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure SpecTec.numtype.I32T
  | I64 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$type_num_clauses»
            SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.I64 a)))
        n (.success (.of SpecTec.numtype.I64T)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:0»
            SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.I64 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_num:clause:1»
          SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.I64 a))
        n (.success (.of SpecTec.numtype.I64T)) n
      unfold SpecTec.«$type_num:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure SpecTec.numtype.I64T
  | F32 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$type_num_clauses»
            SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.F32 a)))
        n (.success (.of SpecTec.numtype.F32T)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:0»
            SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.F32 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:1»
            SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.F32 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:I64»]))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_num:clause:2»
          SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.F32 a))
        n (.success (.of SpecTec.numtype.F32T)) n
      unfold SpecTec.«$type_num:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure SpecTec.numtype.F32T
  | F64 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$type_num_clauses»
            SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.F64 a)))
        n (.success (.of SpecTec.numtype.F64T)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:0»
            SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.F64 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:1»
            SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.F64 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:I64»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:2»
            SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.F64 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:F32»]))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_num:clause:3»
          SpecTec.i32 SpecTec.i64 SpecTec.f32 SpecTec.f64 (.F64 a))
        n (.success (.of SpecTec.numtype.F64T)) n
      unfold SpecTec.«$type_num:clause:3»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure SpecTec.numtype.F64T

theorem const_clause_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.num_) (iit : SpecTec.inferinstrtype)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:78» c irt (.CONST v))
      n (.success (.of iit)) fin) :
    iit.1.INS = (.NoEllipses, []) ∧
    (∃ nt : SpecTec.numtype,
      iit.1.OUTS = (.NoEllipses, [.NumT nt])) ∧
    iit.2 = [] := by
  unfold SpecTec.«Instr_ok:clause:78» at h
  cases h with
  | bind_success hguard htail =>
      cases htail with
      | bind_success htype hpure =>
          cases hpure
          exact ⟨rfl, ⟨_, rfl⟩, rfl⟩

theorem const_clause_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.num_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:78» c irt (.CONST v))
      n (.success (.of
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses, [.NumT (numericType v)]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  unfold SpecTec.«Instr_ok:clause:78»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success (numeric_type_call v n)
  exact SpecTecExecution.Eval.pure _

theorem const_clause_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.num_) (iit : SpecTec.inferinstrtype)
    (n fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Instr_ok:clause:78» c irt (.CONST v))
      n (.success (.of iit)) fin) :
    iit =
      (⟨{ INS := (.NoEllipses, []),
           OUTS := (.NoEllipses, [.NumT (numericType v)]) },
        ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) ∧
    fin = n := by
  obtain ⟨hout, hsupply⟩ :=
    properties.wasm_module_ok.Execution.eval_deterministic h
      (const_clause_total c irt v n)
  cases hout
  exact ⟨rfl, hsupply⟩

end properties.wasm_module_ok.ConstLiteralEffect
