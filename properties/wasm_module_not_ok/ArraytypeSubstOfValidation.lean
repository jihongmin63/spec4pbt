import properties.wasm_module_not_ok.FieldtypeSubstOfValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substArraytypeResult (a : SpecTec.arraytype)
    (dts : List SpecTec.deftype) : Option SpecTec.arraytype :=
  match a with
  | .ArrayT ft => (substFieldtypeResult ft dts).map SpecTec.arraytype.ArrayT

theorem subst_arraytype_of_total (a : SpecTec.arraytype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.arraytype,
        SpecTec.Call.«$subst_arraytype»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» a⟩)
      start (optionOutcome (substArraytypeResult a dts)) start := by
  cases a with
  | ArrayT ft =>
      cases hresult : substFieldtypeResult ft dts with
      | some ft' =>
          have hfield : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨SpecTec.fieldtype,
                SpecTec.Call.«$subst_fieldtype»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ft⟩)
              start (.success (.of ft')) start := by
            simpa [optionOutcome, hresult] using subst_fieldtype_of_total ft dts start
          simp only [substArraytypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.«$subst_arraytype_clauses» (List SpecTec.deftype) dts
                SpecTec.Call.«$subst_of» (.ArrayT ft)))
            start (.success (.of (SpecTec.arraytype.ArrayT ft'))) start
          apply SpecTecExecution.tryClauses_cons_success
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$subst_arraytype:clause:0» (List SpecTec.deftype) dts
              SpecTec.Call.«$subst_of» (.ArrayT ft))
            start (.success (.of (SpecTec.arraytype.ArrayT ft'))) start
          unfold SpecTec.«$subst_arraytype:clause:0»
          apply SpecTecExecution.Eval.bind_success hfield
          exact SpecTecExecution.Eval.pure (SpecTec.arraytype.ArrayT ft')
      | none =>
          have hfield : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨SpecTec.fieldtype,
                SpecTec.Call.«$subst_fieldtype»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ft⟩)
              start .unmatch start := by
            simpa [optionOutcome, hresult] using subst_fieldtype_of_total ft dts start
          simp only [substArraytypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.«$subst_arraytype_clauses» (List SpecTec.deftype) dts
                SpecTec.Call.«$subst_of» (.ArrayT ft)))
            start .unmatch start
          apply SpecTecExecution.tryClauses_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«$subst_arraytype:clause:0» (List SpecTec.deftype) dts
                SpecTec.Call.«$subst_of» (.ArrayT ft)) start .unmatch start
            unfold SpecTec.«$subst_arraytype:clause:0»
            exact SpecTecExecution.Eval.bind_unmatch hfield
          · exact SpecTecExecution.tryClauses_nil start

theorem subst_arraytype_of_deterministic (a : SpecTec.arraytype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.arraytype,
        SpecTec.Call.«$subst_arraytype»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» a⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substArraytypeResult a dts) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_arraytype_of_total a dts start)

end properties.wasm_module_not_ok.Rejection
