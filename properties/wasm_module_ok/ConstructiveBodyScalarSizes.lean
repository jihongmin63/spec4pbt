import properties.wasm_module_ok.ConstructiveBodyOperatorTypes
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyScalarSizes
open SpecTec properties.wasm_module_ok

def numSize : numtype → Int
  | .I32T | .F32T => 4
  | .I64T | .F64T => 8

def packSize : packtype → Int
  | .I8 => 1
  | .I16 => 2
  | .I32 => 4
  | .I64 => 8

theorem num_size (v : numtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Int,SpecTecCall.«$num_size» v⟩) n (.success (.of (numSize v))) n := by
  cases v with
  | I32T =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$num_size_clauses» .I32T) ())
      n (.success (.of (numSize .I32T))) n
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$num_size:clause:0» .I32T) n (.success (.of (numSize .I32T))) n
    unfold SpecTec.«$num_size:clause:0»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
  | I64T =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$num_size_clauses» .I64T) ())
      n (.success (.of (numSize .I64T))) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$num_size:clause:0» .I64T) n .unmatch n
      unfold SpecTec.«$num_size:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$num_size:clause:1» .I64T) n (.success (.of (numSize .I64T))) n
    unfold SpecTec.«$num_size:clause:1»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
  | F32T =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$num_size_clauses» .F32T) ())
      n (.success (.of (numSize .F32T))) n
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$num_size:clause:0» .F32T) n (.success (.of (numSize .F32T))) n
    unfold SpecTec.«$num_size:clause:0»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
  | F64T =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$num_size_clauses» .F64T) ())
      n (.success (.of (numSize .F64T))) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$num_size:clause:0» .F64T) n .unmatch n
      unfold SpecTec.«$num_size:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$num_size:clause:1» .F64T) n (.success (.of (numSize .F64T))) n
    unfold SpecTec.«$num_size:clause:1»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
theorem pack_size (v : packtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Int,SpecTecCall.«$pack_size» v⟩) n (.success (.of (packSize v))) n := by
  cases v with
  | I8 =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$pack_size_clauses» .I8) ())
      n (.success (.of (packSize .I8))) n
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pack_size:clause:0» .I8) n (.success (.of (packSize .I8))) n
    unfold SpecTec.«$pack_size:clause:0»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
  | I16 =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$pack_size_clauses» .I16) ())
      n (.success (.of (packSize .I16))) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pack_size:clause:0» .I16) n .unmatch n
      unfold SpecTec.«$pack_size:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pack_size:clause:1» .I16) n (.success (.of (packSize .I16))) n
    unfold SpecTec.«$pack_size:clause:1»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
  | I32 =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$pack_size_clauses» .I32) ())
      n (.success (.of (packSize .I32))) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pack_size:clause:0» .I32) n .unmatch n
      unfold SpecTec.«$pack_size:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pack_size:clause:1» .I32) n .unmatch n
      unfold SpecTec.«$pack_size:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pack_size:clause:2» .I32) n (.success (.of (packSize .I32))) n
    unfold SpecTec.«$pack_size:clause:2»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
  | I64 =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$pack_size_clauses» .I64) ())
      n (.success (.of (packSize .I64))) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pack_size:clause:0» .I64) n .unmatch n
      unfold SpecTec.«$pack_size:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pack_size:clause:1» .I64) n .unmatch n
      unfold SpecTec.«$pack_size:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pack_size:clause:2» .I64) n .unmatch n
      unfold SpecTec.«$pack_size:clause:2»
      exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«$pack_size:clause:3» .I64) n (.success (.of (packSize .I64))) n
    unfold SpecTec.«$pack_size:clause:3»
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)

theorem pack_ok (size : Nat) (pt : packtype) (n : Nat) (h : packSize pt < (size : Int)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Pack_ok (size : Int) pt⟩) n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Pack_ok_clauses (size : Int) pt) ()) n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_success
  unfold SpecTec.«Pack_ok:clause:0»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
  apply SpecTecExecution.Eval.bind_success (pack_size pt n)
  exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true h) (SpecTecExecution.Eval.pure _)

theorem pack_bad (size : Nat) (pt : packtype) (n : Nat) (h : ¬ packSize pt < (size : Int)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,SpecTecCall.Pack_ok (size : Int) pt⟩) n .unmatch n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Pack_ok_clauses (size : Int) pt) ()) n .unmatch n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · unfold SpecTec.«Pack_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
    apply SpecTecExecution.Eval.bind_success (pack_size pt n)
    exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false h)
  exact SpecTecExecution.Eval.unmatch

#print axioms pack_ok
end properties.wasm_module_ok.ConstructiveBodyScalarSizes
