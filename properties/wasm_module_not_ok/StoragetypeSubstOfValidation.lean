import properties.wasm_module_not_ok.ValtypeSubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substStoragetypeResult (zt : SpecTec.storagetype)
    (dts : List SpecTec.deftype) : Option SpecTec.storagetype :=
  match zt with
  | .ValStorageT t => (substValtypeResult t dts).map SpecTec.storagetype.ValStorageT
  | .PackStorageT pt => some (.PackStorageT pt)

theorem subst_storagetype_of_total (zt : SpecTec.storagetype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.storagetype,
        SpecTec.SpecTecCall.«$subst_storagetype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» zt⟩)
      start (optionOutcome (substStoragetypeResult zt dts)) start := by
  cases zt with
  | ValStorageT t =>
      cases hresult : substValtypeResult t dts with
      | some t' =>
          have hval : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.valtype,
                SpecTec.SpecTecCall.«$subst_valtype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» t⟩)
              start (.success (.of t')) start := by
            simpa [optionOutcome, hresult] using subst_valtype_of_total t dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_storagetype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.ValStorageT t)) ())
            start (optionOutcome (substStoragetypeResult (.ValStorageT t) dts)) start
          simp only [substStoragetypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_storagetype:clause:0» (List SpecTec.deftype) dts
              SpecTec.SpecTecCall.«$subst_of» (.ValStorageT t))
            start (.success (.of (SpecTec.storagetype.ValStorageT t'))) start
          unfold SpecTec.«$subst_storagetype:clause:0»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true
              (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
          · apply SpecTecExecution.Eval.bind_success hval
            exact SpecTecExecution.Eval.pure (SpecTec.storagetype.ValStorageT t')
      | none =>
          have hval : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.valtype,
                SpecTec.SpecTecCall.«$subst_valtype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» t⟩)
              start .unmatch start := by
            simpa [optionOutcome, hresult] using subst_valtype_of_total t dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_storagetype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.ValStorageT t)) ())
            start (optionOutcome (substStoragetypeResult (.ValStorageT t) dts)) start
          simp only [substStoragetypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_storagetype:clause:0» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.ValStorageT t)) start .unmatch start
            unfold SpecTec.«$subst_storagetype:clause:0»
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true
                (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
            · exact SpecTecExecution.Eval.bind_unmatch hval
          · apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$subst_storagetype:clause:1» (List SpecTec.deftype) dts
                  SpecTec.SpecTecCall.«$subst_of» (.ValStorageT t)) start .unmatch start
              unfold SpecTec.«$subst_storagetype:clause:1»
              apply SpecTecExecution.Eval.bind_unmatch
              exact SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:storagetype:PackStorageT»])
            · exact SpecTecExecution.firstSuccess_nil () start
  | PackStorageT pt =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_storagetype_clauses» (List SpecTec.deftype) dts
            SpecTec.SpecTecCall.«$subst_of» (.PackStorageT pt)) ())
        start (optionOutcome (substStoragetypeResult (.PackStorageT pt) dts)) start
      simp only [substStoragetypeResult, optionOutcome]
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_storagetype:clause:0» (List SpecTec.deftype) dts
            SpecTec.SpecTecCall.«$subst_of» (.PackStorageT pt)) start .unmatch start
        unfold SpecTec.«$subst_storagetype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:storagetype:ValStorageT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_storagetype:clause:1» (List SpecTec.deftype) dts
            SpecTec.SpecTecCall.«$subst_of» (.PackStorageT pt))
          start (.success (.of (SpecTec.storagetype.PackStorageT pt))) start
        unfold SpecTec.«$subst_storagetype:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:storagetype:PackStorageT»])
        · exact SpecTecExecution.Eval.pure (SpecTec.storagetype.PackStorageT pt)

theorem subst_storagetype_of_deterministic (zt : SpecTec.storagetype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.storagetype,
        SpecTec.SpecTecCall.«$subst_storagetype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» zt⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substStoragetypeResult zt dts) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_storagetype_of_total zt dts start)

end properties.wasm_module_not_ok.Rejection
