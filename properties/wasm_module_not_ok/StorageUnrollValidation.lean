import properties.wasm_module_not_ok.FunctypeUnrollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def unrollStoragetype (zt : SpecTec.storagetype) (rect : SpecTec.rectype) :
    SpecTec.storagetype :=
  match zt with
  | .ValStorageT t => .ValStorageT (unrollValtype t rect)
  | .PackStorageT pt => .PackStorageT pt

theorem subst_storagetype_unroll_total (zt : SpecTec.storagetype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.storagetype,
        SpecTec.Call.«$subst_storagetype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» zt⟩)
      start (.success (.of (unrollStoragetype zt rect))) start := by
  cases zt with
  | ValStorageT t =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_storagetype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.ValStorageT t)))
        start (.success (.of (unrollStoragetype (.ValStorageT t) rect))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_storagetype:clause:0» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» (.ValStorageT t))
        start (.success (.of (unrollStoragetype (.ValStorageT t) rect))) start
      unfold SpecTec.«$subst_storagetype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
      · apply SpecTecExecution.Eval.bind_success
          (subst_valtype_unroll_total t rect start)
        exact SpecTecExecution.Eval.pure
          (SpecTec.storagetype.ValStorageT (unrollValtype t rect))
  | PackStorageT pt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_storagetype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.PackStorageT pt)))
        start (.success (.of (unrollStoragetype (.PackStorageT pt) rect))) start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_storagetype:clause:0» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.PackStorageT pt)) start .unmatch start
        unfold SpecTec.«$subst_storagetype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_storagetype:clause:1» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.PackStorageT pt))
          start (.success (.of (unrollStoragetype (.PackStorageT pt) rect))) start
        unfold SpecTec.«$subst_storagetype:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:storagetype:PackStorageT»])
        · exact SpecTecExecution.Eval.pure
            (SpecTec.storagetype.PackStorageT pt)

def unrollFieldtype (yt : SpecTec.fieldtype) (rect : SpecTec.rectype) : SpecTec.fieldtype :=
  match yt with
  | .FieldT mutability zt => .FieldT mutability (unrollStoragetype zt rect)

theorem subst_fieldtype_unroll_total (yt : SpecTec.fieldtype)
    (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.fieldtype,
        SpecTec.Call.«$subst_fieldtype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» yt⟩)
      start (.success (.of (unrollFieldtype yt rect))) start := by
  cases yt with
  | FieldT mutability zt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_fieldtype_clauses» SpecTec.rectype rect
            SpecTec.Call.«$s_unroll» (.FieldT mutability zt)))
        start (.success (.of (unrollFieldtype (.FieldT mutability zt) rect))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_fieldtype:clause:0» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» (.FieldT mutability zt))
        start (.success (.of (unrollFieldtype (.FieldT mutability zt) rect))) start
      unfold SpecTec.«$subst_fieldtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (subst_storagetype_unroll_total zt rect start)
      exact SpecTecExecution.Eval.pure
        (SpecTec.fieldtype.FieldT mutability (unrollStoragetype zt rect))

theorem subst_fieldtype_unroll_deterministic (yt : SpecTec.fieldtype)
    (rect : SpecTec.rectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.fieldtype,
        SpecTec.Call.«$subst_fieldtype» SpecTec.rectype rect
          SpecTec.Call.«$s_unroll» yt⟩)
      start outcome finalSupply) :
    outcome = .success (.of (unrollFieldtype yt rect)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_fieldtype_unroll_total yt rect start)

end properties.wasm_module_not_ok.Rejection
