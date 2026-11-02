import properties.wasm_module_not_ok.FunctypeRollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollStoragetype (zt : SpecTec.storagetype) (x y : Nat) :
    SpecTec.storagetype :=
  match zt with
  | .ValStorageT t => .ValStorageT (rollValtype t x y)
  | .PackStorageT pt => .PackStorageT pt

theorem subst_storagetype_roll_total (zt : SpecTec.storagetype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.storagetype,
        SpecTec.Call.«$subst_storagetype» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» zt⟩)
      start (.success (.of (rollStoragetype zt x y))) start := by
  cases zt with
  | ValStorageT t =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_storagetype_clauses» (Nat × Nat) (x, y)
            SpecTec.Call.«$s_roll» (.ValStorageT t)))
        start (.success (.of (rollStoragetype (.ValStorageT t) x y))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_storagetype:clause:0» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» (.ValStorageT t))
        start (.success (.of (rollStoragetype (.ValStorageT t) x y))) start
      unfold SpecTec.«$subst_storagetype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
      · apply SpecTecExecution.Eval.bind_success
          (subst_valtype_roll_total t x y start)
        exact SpecTecExecution.Eval.pure
          (SpecTec.storagetype.ValStorageT (rollValtype t x y))
  | PackStorageT pt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_storagetype_clauses» (Nat × Nat) (x, y)
            SpecTec.Call.«$s_roll» (.PackStorageT pt)))
        start (.success (.of (rollStoragetype (.PackStorageT pt) x y))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_storagetype:clause:0» (Nat × Nat) (x, y)
            SpecTec.Call.«$s_roll» (.PackStorageT pt)) start .unmatch start
        unfold SpecTec.«$subst_storagetype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_storagetype:clause:1» (Nat × Nat) (x, y)
            SpecTec.Call.«$s_roll» (.PackStorageT pt))
          start (.success (.of (rollStoragetype (.PackStorageT pt) x y))) start
        unfold SpecTec.«$subst_storagetype:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:storagetype:PackStorageT»])
        · exact SpecTecExecution.Eval.pure
            (SpecTec.storagetype.PackStorageT pt)

def rollFieldtype (yt : SpecTec.fieldtype) (x y : Nat) : SpecTec.fieldtype :=
  match yt with
  | .FieldT mutability zt => .FieldT mutability (rollStoragetype zt x y)

theorem subst_fieldtype_roll_total (yt : SpecTec.fieldtype)
    (x y start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.fieldtype,
        SpecTec.Call.«$subst_fieldtype» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» yt⟩)
      start (.success (.of (rollFieldtype yt x y))) start := by
  cases yt with
  | FieldT mutability zt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_fieldtype_clauses» (Nat × Nat) (x, y)
            SpecTec.Call.«$s_roll» (.FieldT mutability zt)))
        start (.success (.of (rollFieldtype (.FieldT mutability zt) x y))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_fieldtype:clause:0» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» (.FieldT mutability zt))
        start (.success (.of (rollFieldtype (.FieldT mutability zt) x y))) start
      unfold SpecTec.«$subst_fieldtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_storagetype_roll_total zt x y start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.fieldtype.FieldT mutability (rollStoragetype zt x y))

theorem subst_fieldtype_roll_deterministic (yt : SpecTec.fieldtype)
    (x y start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.fieldtype,
        SpecTec.Call.«$subst_fieldtype» (Nat × Nat) (x, y)
          SpecTec.Call.«$s_roll» yt⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollFieldtype yt x y)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_fieldtype_roll_total yt x y start)

end properties.wasm_module_not_ok.Rejection
