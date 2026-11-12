import properties.wasm_module_ok.ConstructiveBodyOperatorCalls
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyVectorLaneCalls
open SpecTec properties.wasm_module_ok ConstructiveBodyOperatorTypes

def laneCount {A B C D E F : Type} : vecop (laneop A B C D E F) → Nat
  | .V128 (.I8x16 _) => 16
  | .V128 (.I16x8 _) => 8
  | .V128 (.I32x4 _) => 4
  | .V128 (.I64x2 _) => 2
  | .V128 (.F32x4 _) => 4
  | .V128 (.F64x2 _) => 2

theorem lane_count_call {A B C D E F : Type} (op : vecop (laneop A B C D E F)) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Int,Call.«$num_lanes» A B C D E F op⟩) n (.success (.of (laneCount op : Int))) n := by
  cases op with | V128 v =>
   cases v with
   | I8x16 a =>
     apply SpecTecExecution.Eval.call
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«$num_lanes_clauses» A B C D E F (.V128 (.I8x16 a))))
       n (.success (.of (16 : Int))) n
     apply SpecTecExecution.tryClauses_cons_success
     unfold SpecTec.«$num_lanes:clause:0»
     exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | I16x8 a =>
     apply SpecTecExecution.Eval.call
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«$num_lanes_clauses» A B C D E F (.V128 (.I16x8 a))))
       n (.success (.of (8 : Int))) n
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:0»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
     apply SpecTecExecution.tryClauses_cons_success
     unfold SpecTec.«$num_lanes:clause:1»
     exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | I32x4 a =>
     apply SpecTecExecution.Eval.call
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«$num_lanes_clauses» A B C D E F (.V128 (.I32x4 a))))
       n (.success (.of (4 : Int))) n
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:0»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:1»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
     apply SpecTecExecution.tryClauses_cons_success
     unfold SpecTec.«$num_lanes:clause:2»
     exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | I64x2 a =>
     apply SpecTecExecution.Eval.call
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«$num_lanes_clauses» A B C D E F (.V128 (.I64x2 a))))
       n (.success (.of (2 : Int))) n
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:0»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:1»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:2»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
     apply SpecTecExecution.tryClauses_cons_success
     unfold SpecTec.«$num_lanes:clause:3»
     exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | F32x4 a =>
     apply SpecTecExecution.Eval.call
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«$num_lanes_clauses» A B C D E F (.V128 (.F32x4 a))))
       n (.success (.of (4 : Int))) n
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:0»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:1»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:2»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:3»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I64x2»]))
     apply SpecTecExecution.tryClauses_cons_success
     unfold SpecTec.«$num_lanes:clause:4»
     exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | F64x2 a =>
     apply SpecTecExecution.Eval.call
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«$num_lanes_clauses» A B C D E F (.V128 (.F64x2 a))))
       n (.success (.of (2 : Int))) n
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:0»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:1»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:2»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:3»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I64x2»]))
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$num_lanes:clause:4»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:F32x4»]))
     apply SpecTecExecution.tryClauses_cons_success
     unfold SpecTec.«$num_lanes:clause:5»
     exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)

def extractIndex : vextractop_ → Nat
  | .V128 (.I8x16 (.Extract (i,_))) => i
  | .V128 (.I16x8 (.Extract (i,_))) => i
  | .V128 (.I32x4 (.Extract (i,_))) => i
  | .V128 (.I64x2 (.Extract (i,_))) => i
  | .V128 (.F32x4 (.Extract (i,_))) => i
  | .V128 (.F64x2 (.Extract (i,_))) => i

theorem extract_index_call (op : vextractop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Int,Call.«$lane_extractop» op⟩) n (.success (.of (extractIndex op : Int))) n := by
  cases op with | V128 v =>
   cases v with
   | I8x16 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_extractop_clauses» (.V128 (.I8x16 (.Extract (i,x))))))
        n (.success (.of (i : Int))) n
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_extractop:clause:0»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | I16x8 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_extractop_clauses» (.V128 (.I16x8 (.Extract (i,x))))))
        n (.success (.of (i : Int))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_extractop:clause:1»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | I32x4 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_extractop_clauses» (.V128 (.I32x4 (.Extract (i,x))))))
        n (.success (.of (i : Int))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_extractop:clause:2»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | I64x2 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_extractop_clauses» (.V128 (.I64x2 (.Extract (i,x))))))
        n (.success (.of (i : Int))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_extractop:clause:3»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | F32x4 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_extractop_clauses» (.V128 (.F32x4 (.Extract (i,x))))))
        n (.success (.of (i : Int))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I64x2»]))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_extractop:clause:4»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | F64x2 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_extractop_clauses» (.V128 (.F64x2 (.Extract (i,x))))))
        n (.success (.of (i : Int))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I64x2»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_extractop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:F32x4»]))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_extractop:clause:5»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)

def replaceIndex : vreplaceop_ → Nat
  | .V128 (.I8x16 (.Replace i)) => i
  | .V128 (.I16x8 (.Replace i)) => i
  | .V128 (.I32x4 (.Replace i)) => i
  | .V128 (.I64x2 (.Replace i)) => i
  | .V128 (.F32x4 (.Replace i)) => i
  | .V128 (.F64x2 (.Replace i)) => i

theorem replace_index_call (op : vreplaceop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Int,Call.«$lane_replaceop» op⟩) n (.success (.of (replaceIndex op : Int))) n := by
  cases op with | V128 v =>
   cases v with
   | I8x16 a =>
     cases a with | Replace a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_replaceop_clauses» (.V128 (.I8x16 (.Replace a)))))
        n (.success (.of (a : Int))) n
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_replaceop:clause:0»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | I16x8 a =>
     cases a with | Replace a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_replaceop_clauses» (.V128 (.I16x8 (.Replace a)))))
        n (.success (.of (a : Int))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_replaceop:clause:1»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | I32x4 a =>
     cases a with | Replace a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_replaceop_clauses» (.V128 (.I32x4 (.Replace a)))))
        n (.success (.of (a : Int))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_replaceop:clause:2»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | I64x2 a =>
     cases a with | Replace a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_replaceop_clauses» (.V128 (.I64x2 (.Replace a)))))
        n (.success (.of (a : Int))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_replaceop:clause:3»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | F32x4 a =>
     cases a with | Replace a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_replaceop_clauses» (.V128 (.F32x4 (.Replace a)))))
        n (.success (.of (a : Int))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I64x2»]))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_replaceop:clause:4»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
   | F64x2 a =>
     cases a with | Replace a =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$lane_replaceop_clauses» (.V128 (.F64x2 (.Replace a)))))
        n (.success (.of (a : Int))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I16x8»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I32x4»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I64x2»]))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$lane_replaceop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:F32x4»]))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$lane_replaceop:clause:5»
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)

theorem call_value {α : Type} (request : Call α) (expected value : α) (start finish : Nat)
    (total : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨α,request⟩) start (.success (.of expected)) start)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨α,request⟩) start (.success (.of value)) finish) : value=expected ∧ finish=start := by
  obtain ⟨he,hn⟩ := properties.wasm_module_ok.Execution.eval_deterministic h total
  cases he; exact ⟨rfl,hn⟩

theorem extract (c : context) (stack : inferresulttype) (op : vextractop_) (n : Nat)
    (h : extractIndex op < laneCount op) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«VEC.EXTRACT» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T] [.NumT (vecLaneType op)] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.EXTRACT» op) 98 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Instr_ok:clause:98» c stack (.«VEC.EXTRACT» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:98»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  apply SpecTecExecution.Eval.bind_success (vec_lane_type_call op n)
  apply SpecTecExecution.Eval.bind_success (extract_index_call op n)
  apply SpecTecExecution.Eval.bind_success (lane_count_call op n)
  exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by omega)) (SpecTecExecution.Eval.pure _)

theorem extract_original (c : context) (stack : inferresulttype) (op : vextractop_) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«VEC.EXTRACT» op)⟩)
      n (.success (.of result)) finish) :
    extractIndex op < laneCount op ∧ result=ConstructiveBodyControl.effect [.VecT .V128T] [.NumT (vecLaneType op)] [] ∧ finish=n := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«VEC.EXTRACT» op) 98 (by decide) rfl (by decide) result n finish).1 h
  have hb : extractIndex op < laneCount op := by
    change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:98» c stack (.«VEC.EXTRACT» op)) n _ finish at hs
    unfold SpecTec.«Instr_ok:clause:98» at hs
    cases hs with | bind_success hg tail =>
     cases hg
     cases tail with | bind_success _ tail =>
      cases tail with | bind_success _ tail =>
       cases tail with | bind_success hi tail =>
        obtain ⟨he,_⟩ := call_value _ _ _ _ _ (extract_index_call op _) hi
        cases he
        cases tail with | bind_success hc tail =>
         obtain ⟨he,_⟩ := call_value _ _ _ _ _ (lane_count_call op _) hc
         cases he
         cases tail with | bind_success hg _ =>
          cases hg with | guard_true hg => omega
  exact ⟨hb,ConstructiveBodyOperatorCalls.effect_unique c stack (.«VEC.EXTRACT» op) _ result n finish (extract c stack op n hb) h⟩

theorem replace (c : context) (stack : inferresulttype) (op : vreplaceop_) (n : Nat)
    (h : replaceIndex op < laneCount op) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«VEC.REPLACE» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T,.NumT (vecLaneType op)] [.VecT .V128T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.REPLACE» op) 99 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Instr_ok:clause:99» c stack (.«VEC.REPLACE» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:99»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  apply SpecTecExecution.Eval.bind_success (vec_lane_type_call op n)
  apply SpecTecExecution.Eval.bind_success (replace_index_call op n)
  apply SpecTecExecution.Eval.bind_success (lane_count_call op n)
  exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by omega)) (SpecTecExecution.Eval.pure _)

theorem replace_original (c : context) (stack : inferresulttype) (op : vreplaceop_) (result : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«VEC.REPLACE» op)⟩)
      n (.success (.of result)) finish) :
    replaceIndex op < laneCount op ∧ result=ConstructiveBodyControl.effect [.VecT .V128T,.NumT (vecLaneType op)] [.VecT .V128T] [] ∧ finish=n := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack (.«VEC.REPLACE» op) 99 (by decide) rfl (by decide) result n finish).1 h
  have hb : replaceIndex op < laneCount op := by
    change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:99» c stack (.«VEC.REPLACE» op)) n _ finish at hs
    unfold SpecTec.«Instr_ok:clause:99» at hs
    cases hs with | bind_success hg tail =>
     cases hg
     cases tail with | bind_success _ tail =>
      cases tail with | bind_success _ tail =>
       cases tail with | bind_success hi tail =>
        obtain ⟨he,_⟩ := call_value _ _ _ _ _ (replace_index_call op _) hi
        cases he
        cases tail with | bind_success hc tail =>
         obtain ⟨he,_⟩ := call_value _ _ _ _ _ (lane_count_call op _) hc
         cases he
         cases tail with | bind_success hg _ =>
          cases hg with | guard_true hg => omega
  exact ⟨hb,ConstructiveBodyOperatorCalls.effect_unique c stack (.«VEC.REPLACE» op) _ result n finish (replace c stack op n hb) h⟩


#print axioms extract_original
#print axioms replace_original
end properties.wasm_module_ok.ConstructiveBodyVectorLaneCalls
