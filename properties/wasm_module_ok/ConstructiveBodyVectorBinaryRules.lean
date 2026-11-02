import properties.wasm_module_ok.ConstructiveBodyShuffle
import properties.wasm_module_ok.ConstructiveBodyOperatorProductions
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyVectorBinaryRules
open SpecTec properties.wasm_module_ok ConstructiveBodyOperatorTypes

def isShuffle : vbinop_ → Bool
  | .V128 (.I8x16 (.Shuffle _)) => true
  | _ => false

def legal : vbinop_ → Bool
  | .V128 (.I8x16 (.Shuffle xs)) => xs.all (fun x => decide (x<32))
  | _ => true

theorem shuffle_flag (op : vbinop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,Call.«$check_vbop_shuffle» op⟩) n (.success (.of (isShuffle op))) n := by
  cases op with | V128 v =>
   cases v with
   | I8x16 v =>
     cases v with
     | Add =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .Add)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | Sub =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .Sub)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | Mul =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .Mul)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | MinS =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .MinS)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | MinU =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .MinU)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | MaxS =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .MaxS)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | MaxU =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .MaxU)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | AvgrU =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .AvgrU)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | AddSatS =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .AddSatS)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | AddSatU =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .AddSatU)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | SubSatS =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .SubSatS)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | SubSatU =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .SubSatU)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | DotS =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .DotS)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | Q15MulRSatS =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .Q15MulRSatS)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | ExtMulLowS =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .ExtMulLowS)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | ExtMulHighS =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .ExtMulHighS)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | ExtMulLowU =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .ExtMulLowU)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | ExtMulHighU =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .ExtMulHighU)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | Swizzle =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .Swizzle)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | Shuffle xs =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 (.Shuffle xs))))) n (.success (.of true)) n
       apply SpecTecExecution.tryClauses_cons_success
       unfold SpecTec.«$check_vbop_shuffle:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.pure _
     | NarrowS =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .NarrowS)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | NarrowU =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .NarrowU)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | RelaxedSwizzle =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .RelaxedSwizzle)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | RelaxedQ15MulRS =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .RelaxedQ15MulRS)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
     | RelaxedDot =>
       apply SpecTecExecution.Eval.call
       change SpecTecExecution.Eval SpecTec.Body
         (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I8x16 .RelaxedDot)))) n (.success (.of false)) n
       apply SpecTecExecution.tryClauses_cons_unmatch
       · unfold SpecTec.«$check_vbop_shuffle:clause:0»
         apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
         exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
       apply SpecTecExecution.tryClauses_cons_success
       exact SpecTecExecution.Eval.pure _
   | I16x8 v =>
     apply SpecTecExecution.Eval.call
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I16x8 v)))) n (.success (.of false)) n
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$check_vbop_shuffle:clause:0»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
     apply SpecTecExecution.tryClauses_cons_success
     exact SpecTecExecution.Eval.pure _
   | I32x4 v =>
     apply SpecTecExecution.Eval.call
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I32x4 v)))) n (.success (.of false)) n
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$check_vbop_shuffle:clause:0»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
     apply SpecTecExecution.tryClauses_cons_success
     exact SpecTecExecution.Eval.pure _
   | I64x2 v =>
     apply SpecTecExecution.Eval.call
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.I64x2 v)))) n (.success (.of false)) n
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$check_vbop_shuffle:clause:0»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
     apply SpecTecExecution.tryClauses_cons_success
     exact SpecTecExecution.Eval.pure _
   | F32x4 v =>
     apply SpecTecExecution.Eval.call
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.F32x4 v)))) n (.success (.of false)) n
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$check_vbop_shuffle:clause:0»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
     apply SpecTecExecution.tryClauses_cons_success
     exact SpecTecExecution.Eval.pure _
   | F64x2 v =>
     apply SpecTecExecution.Eval.call
     change SpecTecExecution.Eval SpecTec.Body
       (SpecTecExecution.tryClauses (SpecTec.«$check_vbop_shuffle_clauses» (.V128 (.F64x2 v)))) n (.success (.of false)) n
     apply SpecTecExecution.tryClauses_cons_unmatch
     · unfold SpecTec.«$check_vbop_shuffle:clause:0»
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
     apply SpecTecExecution.tryClauses_cons_success
     exact SpecTecExecution.Eval.pure _

theorem head_other (op : vbinop_) (n : Nat) (h : isShuffle op=false) :
    SpecTecExecution.Eval SpecTec.Body (SpecTec.«Vecbinop_ok:clause:0» op) n .unmatch n := by
  cases op with | V128 v =>
   cases v with
   | I8x16 v =>
     cases v with
     | Add =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | Sub =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | Mul =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | MinS =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | MinU =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | MaxS =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | MaxU =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | AvgrU =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | AddSatS =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | AddSatU =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | SubSatS =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | SubSatU =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | DotS =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | Q15MulRSatS =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | ExtMulLowS =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | ExtMulHighS =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | ExtMulLowU =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | ExtMulHighU =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | Swizzle =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | Shuffle xs => cases h
     | NarrowS =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | NarrowU =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | RelaxedSwizzle =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | RelaxedQ15MulRS =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
     | RelaxedDot =>
       unfold SpecTec.«Vecbinop_ok:clause:0»
       apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
       exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:vibinop:Shuffle»]))
   | I16x8 v =>
     unfold SpecTec.«Vecbinop_ok:clause:0»
     exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
   | I32x4 v =>
     unfold SpecTec.«Vecbinop_ok:clause:0»
     exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
   | I64x2 v =>
     unfold SpecTec.«Vecbinop_ok:clause:0»
     exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
   | F32x4 v =>
     unfold SpecTec.«Vecbinop_ok:clause:0»
     exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))
   | F64x2 v =>
     unfold SpecTec.«Vecbinop_ok:clause:0»
     exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:laneop:I8x16»]))

theorem other (op : vbinop_) (n : Nat) (h : isShuffle op=false) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Vecbinop_ok op⟩) n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Vecbinop_ok_clauses op)) n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact head_other op n h
  apply SpecTecExecution.tryClauses_cons_success
  unfold SpecTec.«Vecbinop_ok:clause:1»
  apply SpecTecExecution.Eval.bind_success (shuffle_flag op n)
  exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp [h])) (SpecTecExecution.Eval.pure _)

theorem shuffle_outcome (xs : List Nat) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Vecbinop_ok (.V128 (.I8x16 (.Shuffle xs)))⟩)
      n (if xs.all (fun x => decide (x<32)) then .success (.of ()) else .unmatch) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Vecbinop_ok_clauses (.V128 (.I8x16 (.Shuffle xs))))) n _ n
  cases h : xs.all (fun x => decide (x<32)) with
  | true =>
    simp only [h,Bool.true_eq,ite_true]
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Vecbinop_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (ConstructiveBodyShuffle.indices_call xs n)
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true h) (SpecTecExecution.Eval.pure _)
  | false =>
    simp only [h,Bool.false_eq_true,ite_false]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Vecbinop_ok:clause:0»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      apply SpecTecExecution.Eval.bind_success (ConstructiveBodyShuffle.indices_call xs n)
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [h]))
    apply SpecTecExecution.tryClauses_cons_unmatch
    · unfold SpecTec.«Vecbinop_ok:clause:1»
      apply SpecTecExecution.Eval.bind_success (shuffle_flag (.V128 (.I8x16 (.Shuffle xs))) n)
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [isShuffle]))
    exact SpecTecExecution.Eval.unmatch

theorem outcome (op : vbinop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Vecbinop_ok op⟩)
      n (if legal op then .success (.of ()) else .unmatch) n := by
  cases op with | V128 v =>
   cases v with
   | I8x16 v =>
     cases v <;> first
       | exact shuffle_outcome _ n
       | exact other _ n rfl
   | I16x8 v => exact other _ n rfl
   | I32x4 v => exact other _ n rfl
   | I64x2 v => exact other _ n rfl
   | F32x4 v => exact other _ n rfl
   | F64x2 v => exact other _ n rfl

theorem exact_call (op : vbinop_) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,Call.Vecbinop_ok op⟩) n (.success (.of ())) finish ↔ legal op=true ∧ finish=n := by
  constructor
  · intro h
    obtain ⟨he,hn⟩ := properties.wasm_module_ok.Execution.eval_deterministic h (outcome op n)
    cases hl : legal op <;> simp [hl] at he
    exact ⟨rfl,hn⟩
  · rintro ⟨hl,hn⟩; subst finish
    simpa [hl] using outcome op n

theorem binary (c : context) (stack : inferresulttype) (op : vbinop_) (n : Nat) (h : legal op=true) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«VEC.BINARY» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.VecT .V128T,.VecT .V128T] [.VecT .V128T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«VEC.BINARY» op) 87 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Instr_ok:clause:87» c stack (.«VEC.BINARY» op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:87»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success ((exact_call op n n).2 ⟨h,rfl⟩)
  apply SpecTecExecution.Eval.bind_success (vector_type_call op n)
  exact SpecTecExecution.Eval.pure _

#print axioms exact_call
end properties.wasm_module_ok.ConstructiveBodyVectorBinaryRules
