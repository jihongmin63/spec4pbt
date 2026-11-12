import properties.wasm_module_ok.ArrayTypeDecision
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.UnpackedFieldDecision

def unpackedStorageResult : SpecTec.storagetype → SpecTec.valtype
  | .ValStorageT t => t
  | .PackStorageT _ => .NumT .I32T

def unpackedFieldResult : SpecTec.fieldtype → SpecTec.valtype
  | .FieldT _ st => unpackedStorageResult st

theorem unpacked_storage_total (st : SpecTec.storagetype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.valtype,
        SpecTec.Call.«$unpacked_storage_type» st⟩)
      n (.success (.of (unpackedStorageResult st))) n := by
  cases st with
  | ValStorageT t =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$unpacked_storage_type_clauses» (.ValStorageT t)))
      n (.success (.of t)) n
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$unpacked_storage_type:clause:0» (.ValStorageT t))
      n (.success (.of t)) n
    unfold SpecTec.«$unpacked_storage_type:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · exact SpecTecExecution.Eval.pure t
  | PackStorageT pt =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$unpacked_storage_type_clauses» (.PackStorageT pt)))
      n (.success (.of (SpecTec.valtype.NumT .I32T))) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$unpacked_storage_type:clause:0» (.PackStorageT pt))
        n .unmatch n
      unfold SpecTec.«$unpacked_storage_type:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$unpacked_storage_type:clause:1» (.PackStorageT pt))
        n (.success (.of (SpecTec.valtype.NumT .I32T))) n
      unfold SpecTec.«$unpacked_storage_type:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure _

theorem unpacked_field_total (ft : SpecTec.fieldtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.valtype,
        SpecTec.Call.«$unpacked_field_type» ft⟩)
      n (.success (.of (unpackedFieldResult ft))) n := by
  cases ft with
  | FieldT m st =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$unpacked_field_type_clauses» (.FieldT m st)))
      n (.success (.of (unpackedStorageResult st))) n
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$unpacked_field_type:clause:0» (.FieldT m st))
      n (.success (.of (unpackedStorageResult st))) n
    unfold SpecTec.«$unpacked_field_type:clause:0»
    apply SpecTecExecution.Eval.bind_success
      (unpacked_storage_total st n)
    exact SpecTecExecution.Eval.pure _

theorem unpacked_field_success_iff_result
    (ft : SpecTec.fieldtype) (out : SpecTec.valtype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.valtype,
        SpecTec.Call.«$unpacked_field_type» ft⟩)
      n (.success (.of out)) finalSupply ↔
    out = unpackedFieldResult ft ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (unpacked_field_total ft n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact unpacked_field_total ft finalSupply

end properties.wasm_module_ok.UnpackedFieldDecision
