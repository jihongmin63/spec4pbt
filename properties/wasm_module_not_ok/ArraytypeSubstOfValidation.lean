import properties.wasm_module_not_ok.FieldtypeSubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substArraytypeResult (a : SpecTec.arraytype)
    (dts : List SpecTec.deftype) : Option SpecTec.arraytype :=
  match a with
  | .ArrayT ft => (substFieldtypeResult ft dts).map SpecTec.arraytype.ArrayT

theorem subst_arraytype_of_total (a : SpecTec.arraytype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.arraytype,
        SpecTec.SpecTecCall.«$subst_arraytype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» a⟩)
      start (optionOutcome (substArraytypeResult a dts)) start := by
  cases a with
  | ArrayT ft =>
      cases hresult : substFieldtypeResult ft dts with
      | some ft' =>
          have hfield : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.fieldtype,
                SpecTec.SpecTecCall.«$subst_fieldtype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» ft⟩)
              start (.success (.of ft')) start := by
            simpa [optionOutcome, hresult] using subst_fieldtype_of_total ft dts start
          simp only [substArraytypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_arraytype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.ArrayT ft)) ())
            start (.success (.of (SpecTec.arraytype.ArrayT ft'))) start
          apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_arraytype:clause:0» (List SpecTec.deftype) dts
              SpecTec.SpecTecCall.«$subst_of» (.ArrayT ft))
            start (.success (.of (SpecTec.arraytype.ArrayT ft'))) start
          unfold SpecTec.«$subst_arraytype:clause:0»
          apply SpecTecExecution.Eval.bind_success hfield
          exact SpecTecExecution.Eval.pure (SpecTec.arraytype.ArrayT ft')
      | none =>
          have hfield : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.fieldtype,
                SpecTec.SpecTecCall.«$subst_fieldtype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» ft⟩)
              start .unmatch start := by
            simpa [optionOutcome, hresult] using subst_fieldtype_of_total ft dts start
          simp only [substArraytypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_arraytype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.ArrayT ft)) ())
            start .unmatch start
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_arraytype:clause:0» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.ArrayT ft)) start .unmatch start
            unfold SpecTec.«$subst_arraytype:clause:0»
            exact SpecTecExecution.Eval.bind_unmatch hfield
          · exact SpecTecExecution.firstSuccess_nil () start

theorem subst_arraytype_of_deterministic (a : SpecTec.arraytype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.arraytype,
        SpecTec.SpecTecCall.«$subst_arraytype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» a⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substArraytypeResult a dts) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_arraytype_of_total a dts start)

end properties.wasm_module_not_ok.Rejection
