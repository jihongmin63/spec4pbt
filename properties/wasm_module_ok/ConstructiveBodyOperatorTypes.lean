import properties.wasm_module_ok.ConstructiveBodyRoute

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstructiveBodyOperatorTypes

def numericType {A B C D : Type} : SpecTec.op A B C D → SpecTec.numtype
  | .I32 _ => .I32T
  | .I64 _ => .I64T
  | .F32 _ => .F32T
  | .F64 _ => .F64T

theorem numeric_type_call {A B C D : Type} (v : SpecTec.op A B C D) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.numtype,
        SpecTec.Call.«$type_num»
          A B C D v⟩)
      n (.success (.of (numericType v))) n := by
  cases v with
  | I32 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$type_num_clauses»
            A B C D (.I32 a)))
        n (.success (.of SpecTec.numtype.I32T)) n
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_num:clause:0»
          A B C D (.I32 a))
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
            A B C D (.I64 a)))
        n (.success (.of SpecTec.numtype.I64T)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:0»
            A B C D (.I64 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_num:clause:1»
          A B C D (.I64 a))
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
            A B C D (.F32 a)))
        n (.success (.of SpecTec.numtype.F32T)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:0»
            A B C D (.F32 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:1»
            A B C D (.F32 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:I64»]))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_num:clause:2»
          A B C D (.F32 a))
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
            A B C D (.F64 a)))
        n (.success (.of SpecTec.numtype.F64T)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:0»
            A B C D (.F64 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:I32»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:1»
            A B C D (.F64 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:I64»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_num:clause:2»
            A B C D (.F64 a))
          n .unmatch n
        unfold SpecTec.«$type_num:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:op:F32»]))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_num:clause:3»
          A B C D (.F64 a))
        n (.success (.of SpecTec.numtype.F64T)) n
      unfold SpecTec.«$type_num:clause:3»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure SpecTec.numtype.F64T

theorem vector_type_call {A : Type} (v : SpecTec.vecop A) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.vectype,SpecTec.Call.«$type_vecop» A v⟩)
      n (.success (.of SpecTec.vectype.V128T)) n := by
  cases v with
  | V128 a =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.«$type_vecop_clauses» A (.V128 a)))
      n (.success (.of SpecTec.vectype.V128T)) n
    apply SpecTecExecution.tryClauses_cons_success
    exact SpecTecExecution.Eval.pure _

open SpecTec

def laneType {A B C D E F : Type} : laneop A B C D E F → numtype
  | .I8x16 _ | .I16x8 _ | .I32x4 _ => .I32T
  | .I64x2 _ => .I64T
  | .F32x4 _ => .F32T
  | .F64x2 _ => .F64T

theorem lane_type_call {A B C D E F : Type} (v : laneop A B C D E F) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨numtype,Call.«$type_lane» A B C D E F v⟩)
      n (.success (.of (laneType v))) n := by
  cases v with
  | I8x16 a =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.«$type_lane_clauses» A B C D E F (.I8x16 a)))
      n (.success (.of numtype.I32T)) n
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$type_lane:clause:0» A B C D E F (.I8x16 a)) n (.success (.of numtype.I32T)) n
    unfold SpecTec.«$type_lane:clause:0»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
  | I16x8 a =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.«$type_lane_clauses» A B C D E F (.I16x8 a)))
      n (.success (.of numtype.I32T)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:0» A B C D E F (.I16x8 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$type_lane:clause:1» A B C D E F (.I16x8 a)) n (.success (.of numtype.I32T)) n
    unfold SpecTec.«$type_lane:clause:1»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
  | I32x4 a =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.«$type_lane_clauses» A B C D E F (.I32x4 a)))
      n (.success (.of numtype.I32T)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:0» A B C D E F (.I32x4 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:1» A B C D E F (.I32x4 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$type_lane:clause:2» A B C D E F (.I32x4 a)) n (.success (.of numtype.I32T)) n
    unfold SpecTec.«$type_lane:clause:2»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
  | I64x2 a =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.«$type_lane_clauses» A B C D E F (.I64x2 a)))
      n (.success (.of numtype.I64T)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:0» A B C D E F (.I64x2 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:1» A B C D E F (.I64x2 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:2» A B C D E F (.I64x2 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:2»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$type_lane:clause:3» A B C D E F (.I64x2 a)) n (.success (.of numtype.I64T)) n
    unfold SpecTec.«$type_lane:clause:3»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
  | F32x4 a =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.«$type_lane_clauses» A B C D E F (.F32x4 a)))
      n (.success (.of numtype.F32T)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:0» A B C D E F (.F32x4 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:1» A B C D E F (.F32x4 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:2» A B C D E F (.F32x4 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:2»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:3» A B C D E F (.F32x4 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:3»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I64x2»]))
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$type_lane:clause:4» A B C D E F (.F32x4 a)) n (.success (.of numtype.F32T)) n
    unfold SpecTec.«$type_lane:clause:4»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
  | F64x2 a =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.«$type_lane_clauses» A B C D E F (.F64x2 a)))
      n (.success (.of numtype.F64T)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:0» A B C D E F (.F64x2 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:1» A B C D E F (.F64x2 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:2» A B C D E F (.F64x2 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:2»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:3» A B C D E F (.F64x2 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:3»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I64x2»]))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_lane:clause:4» A B C D E F (.F64x2 a)) n .unmatch n
      unfold SpecTec.«$type_lane:clause:4»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:F32x4»]))
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$type_lane:clause:5» A B C D E F (.F64x2 a)) n (.success (.of numtype.F64T)) n
    unfold SpecTec.«$type_lane:clause:5»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)

def vecLaneType {A B C D E F : Type} : vecop (laneop A B C D E F) → numtype
  | .V128 v => laneType v

theorem vec_lane_type_call {A B C D E F : Type} (v : vecop (laneop A B C D E F)) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨numtype,Call.«$type_vec_lane» A B C D E F v⟩)
      n (.success (.of (vecLaneType v))) n := by
  cases v with
  | V128 v =>
    cases v with
    | I8x16 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_vec_lane_clauses» A B C D E F (.V128 (.I8x16 a))))
        n (.success (.of numtype.I32T)) n
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_vec_lane:clause:0» A B C D E F (.V128 (.I8x16 a))) n (.success (.of numtype.I32T)) n
      unfold SpecTec.«$type_vec_lane:clause:0»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (lane_type_call (.I8x16 a) n) (SpecTecExecution.Eval.pure _)
    | I16x8 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_vec_lane_clauses» A B C D E F (.V128 (.I16x8 a))))
        n (.success (.of numtype.I32T)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:0» A B C D E F (.V128 (.I16x8 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_vec_lane:clause:1» A B C D E F (.V128 (.I16x8 a))) n (.success (.of numtype.I32T)) n
      unfold SpecTec.«$type_vec_lane:clause:1»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (lane_type_call (.I16x8 a) n) (SpecTecExecution.Eval.pure _)
    | I32x4 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_vec_lane_clauses» A B C D E F (.V128 (.I32x4 a))))
        n (.success (.of numtype.I32T)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:0» A B C D E F (.V128 (.I32x4 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:1» A B C D E F (.V128 (.I32x4 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_vec_lane:clause:2» A B C D E F (.V128 (.I32x4 a))) n (.success (.of numtype.I32T)) n
      unfold SpecTec.«$type_vec_lane:clause:2»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (lane_type_call (.I32x4 a) n) (SpecTecExecution.Eval.pure _)
    | I64x2 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_vec_lane_clauses» A B C D E F (.V128 (.I64x2 a))))
        n (.success (.of numtype.I64T)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:0» A B C D E F (.V128 (.I64x2 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:1» A B C D E F (.V128 (.I64x2 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:2» A B C D E F (.V128 (.I64x2 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I32x4»]))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_vec_lane:clause:3» A B C D E F (.V128 (.I64x2 a))) n (.success (.of numtype.I64T)) n
      unfold SpecTec.«$type_vec_lane:clause:3»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (lane_type_call (.I64x2 a) n) (SpecTecExecution.Eval.pure _)
    | F32x4 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_vec_lane_clauses» A B C D E F (.V128 (.F32x4 a))))
        n (.success (.of numtype.F32T)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:0» A B C D E F (.V128 (.F32x4 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:1» A B C D E F (.V128 (.F32x4 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:2» A B C D E F (.V128 (.F32x4 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I32x4»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:3» A B C D E F (.V128 (.F32x4 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I64x2»]))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_vec_lane:clause:4» A B C D E F (.V128 (.F32x4 a))) n (.success (.of numtype.F32T)) n
      unfold SpecTec.«$type_vec_lane:clause:4»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (lane_type_call (.F32x4 a) n) (SpecTecExecution.Eval.pure _)
    | F64x2 a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_vec_lane_clauses» A B C D E F (.V128 (.F64x2 a))))
        n (.success (.of numtype.F64T)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:0» A B C D E F (.V128 (.F64x2 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:1» A B C D E F (.V128 (.F64x2 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:2» A B C D E F (.V128 (.F64x2 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I32x4»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:3» A B C D E F (.V128 (.F64x2 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:I64x2»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$type_vec_lane:clause:4» A B C D E F (.V128 (.F64x2 a))) n .unmatch n
        unfold SpecTec.«$type_vec_lane:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:laneop:F32x4»]))
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$type_vec_lane:clause:5» A B C D E F (.V128 (.F64x2 a))) n (.success (.of numtype.F64T)) n
      unfold SpecTec.«$type_vec_lane:clause:5»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (lane_type_call (.F64x2 a) n) (SpecTecExecution.Eval.pure _)

#print axioms numeric_type_call
#print axioms lane_type_call
end properties.wasm_module_ok.ConstructiveBodyOperatorTypes
