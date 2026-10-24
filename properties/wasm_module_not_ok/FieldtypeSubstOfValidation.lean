import properties.wasm_module_not_ok.StoragetypeSubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substFieldtypeResult (ft : SpecTec.fieldtype)
    (dts : List SpecTec.deftype) : Option SpecTec.fieldtype :=
  match ft with
  | .FieldT mu zt => (substStoragetypeResult zt dts).map (SpecTec.fieldtype.FieldT mu)

theorem subst_fieldtype_of_total (ft : SpecTec.fieldtype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.fieldtype,
        SpecTec.SpecTecCall.«$subst_fieldtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» ft⟩)
      start (optionOutcome (substFieldtypeResult ft dts)) start := by
  cases ft with
  | FieldT mu zt =>
      cases hresult : substStoragetypeResult zt dts with
      | some zt' =>
          have hstorage : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.storagetype,
                SpecTec.SpecTecCall.«$subst_storagetype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» zt⟩)
              start (.success (.of zt')) start := by
            simpa [optionOutcome, hresult] using subst_storagetype_of_total zt dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_fieldtype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.FieldT mu zt)) ())
            start (optionOutcome (substFieldtypeResult (.FieldT mu zt) dts)) start
          simp only [substFieldtypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_fieldtype:clause:0» (List SpecTec.deftype) dts
              SpecTec.SpecTecCall.«$subst_of» (.FieldT mu zt))
            start (.success (.of (SpecTec.fieldtype.FieldT mu zt'))) start
          unfold SpecTec.«$subst_fieldtype:clause:0»
          apply SpecTecExecution.Eval.bind_success hstorage
          exact SpecTecExecution.Eval.pure (SpecTec.fieldtype.FieldT mu zt')
      | none =>
          have hstorage : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.storagetype,
                SpecTec.SpecTecCall.«$subst_storagetype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» zt⟩)
              start .unmatch start := by
            simpa [optionOutcome, hresult] using subst_storagetype_of_total zt dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_fieldtype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.FieldT mu zt)) ())
            start (optionOutcome (substFieldtypeResult (.FieldT mu zt) dts)) start
          simp only [substFieldtypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_fieldtype:clause:0» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.FieldT mu zt)) start .unmatch start
            unfold SpecTec.«$subst_fieldtype:clause:0»
            exact SpecTecExecution.Eval.bind_unmatch hstorage
          · exact SpecTecExecution.firstSuccess_nil () start

theorem subst_fieldtype_of_deterministic (ft : SpecTec.fieldtype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.fieldtype,
        SpecTec.SpecTecCall.«$subst_fieldtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» ft⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substFieldtypeResult ft dts) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_fieldtype_of_total ft dts start)

end properties.wasm_module_not_ok.Rejection
