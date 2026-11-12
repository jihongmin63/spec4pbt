import properties.wasm_module_ok.ConstructiveBodyOperatorProductions
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyConversionTypes
open SpecTec properties.wasm_module_ok

/-- A signature table used for proof and structural operator planning. The
constructor below enumerates the twelve source signature alternatives directly. -/
def typeOf : cvtop_ → Option (numtype × numtype)
  | .I32 .WrapI64 => some (.I64T,.I32T)
  | .I32 .TruncSF32 | .I32 .TruncUF32 | .I32 .TruncSatSF32 | .I32 .TruncSatUF32 | .I32 .ReinterpretFloat => some (.F32T,.I32T)
  | .I32 .TruncSF64 | .I32 .TruncUF64 | .I32 .TruncSatSF64 | .I32 .TruncSatUF64 => some (.F64T,.I32T)
  | .I64 .ExtendSI32 | .I64 .ExtendUI32 => some (.I32T,.I64T)
  | .I64 .TruncSF32 | .I64 .TruncUF32 | .I64 .TruncSatSF32 | .I64 .TruncSatUF32 => some (.F32T,.I64T)
  | .I64 .TruncSF64 | .I64 .TruncUF64 | .I64 .TruncSatSF64 | .I64 .TruncSatUF64 | .I64 .ReinterpretFloat => some (.F64T,.I64T)
  | .F32 .ConvertSI32 | .F32 .ConvertUI32 | .F32 .ReinterpretInt => some (.I32T,.F32T)
  | .F32 .ConvertSI64 | .F32 .ConvertUI64 => some (.I64T,.F32T)
  | .F32 .DemoteF64 => some (.F64T,.F32T)
  | .F64 .ConvertSI32 | .F64 .ConvertUI32 => some (.I32T,.F64T)
  | .F64 .ConvertSI64 | .F64 .ConvertUI64 | .F64 .ReinterpretInt => some (.I64T,.F64T)
  | .F64 .PromoteF32 => some (.F32T,.F64T)
  | _ => none

theorem type_outcome (op : cvtop_) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨numtype × numtype,Call.«$type_cvtop» op⟩) n
      (match typeOf op with | some ts => .success (.of ts) | none => .unmatch) n := by
  cases op with
  | I32 op =>
    cases op with
    | ExtendSI32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .ExtendSI32))) n (.unmatch) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:8»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:9»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:10»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:11»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      exact SpecTecExecution.Eval.unmatch
    | ExtendUI32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .ExtendUI32))) n (.unmatch) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:8»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:9»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:10»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:11»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      exact SpecTecExecution.Eval.unmatch
    | WrapI64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .WrapI64))) n (.success (.of ((.I64T,.I32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:0»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncSF32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .TruncSF32))) n (.success (.of ((.F32T,.I32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:1»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncUF32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .TruncUF32))) n (.success (.of ((.F32T,.I32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:1»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncSF64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .TruncSF64))) n (.success (.of ((.F64T,.I32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:2»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncUF64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .TruncUF64))) n (.success (.of ((.F64T,.I32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:2»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncSatSF32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .TruncSatSF32))) n (.success (.of ((.F32T,.I32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:1»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncSatUF32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .TruncSatUF32))) n (.success (.of ((.F32T,.I32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:1»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncSatSF64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .TruncSatSF64))) n (.success (.of ((.F64T,.I32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:2»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncSatUF64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .TruncSatUF64))) n (.success (.of ((.F64T,.I32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:2»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | ReinterpretFloat =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I32 .ReinterpretFloat))) n (.success (.of ((.F32T,.I32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:1»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
  | I64 op =>
    cases op with
    | ExtendSI32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .ExtendSI32))) n (.success (.of ((.I32T,.I64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:3»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | ExtendUI32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .ExtendUI32))) n (.success (.of ((.I32T,.I64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:3»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | WrapI64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .WrapI64))) n (.unmatch) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:8»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:9»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:10»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:11»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      exact SpecTecExecution.Eval.unmatch
    | TruncSF32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .TruncSF32))) n (.success (.of ((.F32T,.I64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:4»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncUF32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .TruncUF32))) n (.success (.of ((.F32T,.I64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:4»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncSF64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .TruncSF64))) n (.success (.of ((.F64T,.I64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:5»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncUF64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .TruncUF64))) n (.success (.of ((.F64T,.I64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:5»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncSatSF32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .TruncSatSF32))) n (.success (.of ((.F32T,.I64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:4»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncSatUF32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .TruncSatUF32))) n (.success (.of ((.F32T,.I64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:4»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncSatSF64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .TruncSatSF64))) n (.success (.of ((.F64T,.I64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:5»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | TruncSatUF64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .TruncSatUF64))) n (.success (.of ((.F64T,.I64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:5»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | ReinterpretFloat =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.I64 .ReinterpretFloat))) n (.success (.of ((.F64T,.I64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:5»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
  | F32 op =>
    cases op with
    | ConvertSI32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F32 .ConvertSI32))) n (.success (.of ((.I32T,.F32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:6»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | ConvertUI32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F32 .ConvertUI32))) n (.success (.of ((.I32T,.F32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:6»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | ConvertSI64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F32 .ConvertSI64))) n (.success (.of ((.I64T,.F32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:7»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | ConvertUI64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F32 .ConvertUI64))) n (.success (.of ((.I64T,.F32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:7»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | PromoteF32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F32 .PromoteF32))) n (.unmatch) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:8»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:9»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:10»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:11»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      exact SpecTecExecution.Eval.unmatch
    | DemoteF64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F32 .DemoteF64))) n (.success (.of ((.F64T,.F32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:8»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | ReinterpretInt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F32 .ReinterpretInt))) n (.success (.of ((.I32T,.F32T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:6»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
  | F64 op =>
    cases op with
    | ConvertSI32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F64 .ConvertSI32))) n (.success (.of ((.I32T,.F64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:8»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:9»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | ConvertUI32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F64 .ConvertUI32))) n (.success (.of ((.I32T,.F64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:8»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:9»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | ConvertSI64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F64 .ConvertSI64))) n (.success (.of ((.I64T,.F64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:8»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:9»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:10»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | ConvertUI64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F64 .ConvertUI64))) n (.success (.of ((.I64T,.F64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:8»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:9»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:10»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | PromoteF32 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F64 .PromoteF32))) n (.success (.of ((.F32T,.F64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:8»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:9»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:10»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:11»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
    | DemoteF64 =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F64 .DemoteF64))) n (.unmatch) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:8»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:9»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:10»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:11»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      exact SpecTecExecution.Eval.unmatch
    | ReinterpretInt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.«$type_cvtop_clauses» (.F64 .ReinterpretInt))) n (.success (.of ((.I64T,.F64T) : numtype × numtype))) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:1»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:2»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:3»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:4»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:5»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:6»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:7»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:8»
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_unmatch
      · unfold SpecTec.«$type_cvtop:clause:9»
        apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
        exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
      apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«$type_cvtop:clause:10»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)

theorem type_exact (op : cvtop_) (ts : numtype × numtype) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨numtype × numtype,Call.«$type_cvtop» op⟩) n (.success (.of ts)) finish ↔
    typeOf op=some ts ∧ finish=n := by
  constructor
  · intro h
    obtain ⟨he,hn⟩ := properties.wasm_module_ok.Execution.eval_deterministic h (type_outcome op n)
    cases ht : typeOf op with
    | none => simp [ht] at he
    | some t => simp only [ht] at he; cases he; exact ⟨rfl,hn⟩
  · rintro ⟨ht,hn⟩; subst finish
    simpa [ht] using type_outcome op n

theorem convert (c : context) (stack : inferresulttype) (op : cvtop_) (ts : numtype × numtype) (n : Nat)
    (ht : typeOf op=some ts) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.CONVERT op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.NumT ts.1] [.NumT ts.2] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.CONVERT op) 83 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Instr_ok:clause:83» c stack (.CONVERT op)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:83»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success ((type_exact op ts n n).2 ⟨ht,rfl⟩)
  exact SpecTecExecution.Eval.pure _

#print axioms type_exact
end properties.wasm_module_ok.ConstructiveBodyConversionTypes
