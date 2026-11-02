import properties.wasm_module_not_ok.StorageValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def fieldtypeValid (c : SpecTec.context) (yt : SpecTec.fieldtype) : Bool :=
  match yt with
  | .FieldT _ zt => storagetypeValid c zt

theorem fieldtype_ok_success_iff_valid (c : SpecTec.context)
    (yt : SpecTec.fieldtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Fieldtype_ok c yt⟩)
      start (.success (.of ())) finalSupply ↔
    fieldtypeValid c yt = true ∧ finalSupply = start := by
  cases yt with
  | FieldT mutability zt =>
      constructor
      · intro h
        cases h with
        | call hbody =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«Fieldtype_ok:clause:0» c (.FieldT mutability zt))
              (fun _ => .unmatch))
            start (.success (.of ())) finalSupply at hbody
          cases hbody with
          | orElse_success hfirst =>
            unfold SpecTec.«Fieldtype_ok:clause:0» at hfirst
            cases hfirst with
            | bind_success hstorage hpure =>
              cases hpure with
              | pure =>
                simpa [fieldtypeValid] using
                  (storagetype_ok_success_iff_valid c zt start finalSupply).1
                    hstorage
          | orElse_unmatch _ htail => cases htail
      · rintro ⟨hvalid, rfl⟩
        have hstorage :=
          (storagetype_ok_success_iff_valid c zt finalSupply finalSupply).2
            ⟨by simpa [fieldtypeValid] using hvalid, rfl⟩
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Fieldtype_ok_clauses c (.FieldT mutability zt)) ())
          finalSupply (.success (.of ())) finalSupply
        apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Fieldtype_ok:clause:0» c (.FieldT mutability zt))
          finalSupply (.success (.of ())) finalSupply
        unfold SpecTec.«Fieldtype_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success hstorage
        exact SpecTecExecution.Eval.pure ()

end properties.wasm_module_not_ok.Rejection
