import properties.wasm_module_ok.StoragetypeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.FieldtypeValidation

def fieldtypeValid (c : SpecTec.context) : SpecTec.fieldtype → Bool
  | .FieldT _ zt => StoragetypeValidation.storagetypeValid c zt

theorem fieldtype_storage_success_iff
    (c : SpecTec.context) (m : SpecTec.«mut»)
    (zt : SpecTec.storagetype) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Fieldtype_ok c (.FieldT m zt)⟩)
      n (.success (.of ())) finish ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Storagetype_ok c zt⟩)
      n (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.firstSuccess_success_iff
          (SpecTec.Fieldtype_ok_clauses c (.FieldT m zt)) ()
          n (.of ()) finish).1 hbody
      unfold SpecTec.Fieldtype_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«Fieldtype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hstorage hpure =>
          cases hpure
          exact hstorage
      | next _ hnone => cases hnone
  · intro hstorage
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Fieldtype_ok_clauses c (.FieldT m zt)) ())
      n (.success (.of ())) finish
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Fieldtype_ok:clause:0» c (.FieldT m zt))
      n (.success (.of ())) finish
    unfold SpecTec.«Fieldtype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success hstorage
    exact SpecTecExecution.Eval.pure ()

theorem fieldtype_success_iff_valid
    (c : SpecTec.context) (ft : SpecTec.fieldtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Fieldtype_ok c ft⟩)
      n (.success (.of ())) finish ↔
    fieldtypeValid c ft = true ∧ finish = n := by
  cases ft with
  | FieldT m zt =>
    rw [fieldtype_storage_success_iff,
      StoragetypeValidation.storagetype_success_iff_valid]
    rfl

end properties.wasm_module_ok.FieldtypeValidation
