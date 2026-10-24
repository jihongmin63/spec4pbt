import properties.wasm_module_not_ok.StructtypeSubstOfValidation
import properties.wasm_module_not_ok.ArraytypeSubstOfValidation
import properties.wasm_module_not_ok.FunctypeSubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substStrtypeResult (st : SpecTec.strtype)
    (dts : List SpecTec.deftype) : Option SpecTec.strtype :=
  match st with
  | .DefStructT st => (substStructtypeResult st dts).map SpecTec.strtype.DefStructT
  | .DefArrayT arr => (substArraytypeResult arr dts).map SpecTec.strtype.DefArrayT
  | .DefFuncT ft => (substFunctypeResult ft dts).map SpecTec.strtype.DefFuncT

theorem subst_strtype_of_total (st : SpecTec.strtype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype,
        SpecTec.SpecTecCall.«$subst_strtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» st⟩)
      start (optionOutcome (substStrtypeResult st dts)) start := by
  cases st with
  | DefStructT st =>
      cases hresult : substStructtypeResult st dts with
      | some stp =>
          have hchild : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.structtype,
                SpecTec.SpecTecCall.«$subst_structtype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» st⟩)
              start (.success (.of stp)) start := by
            simpa [optionOutcome, hresult] using subst_structtype_of_total st dts start
          simp only [substStrtypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_strtype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefStructT st)) ())
            start (.success (.of (SpecTec.strtype.DefStructT stp))) start
          apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_strtype:clause:0» (List SpecTec.deftype) dts
              SpecTec.SpecTecCall.«$subst_of» (.DefStructT st))
            start (.success (.of (SpecTec.strtype.DefStructT stp))) start
          unfold SpecTec.«$subst_strtype:clause:0»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true
              (by simp [SpecTec.«exec:match:strtype:DefStructT»])
          · apply SpecTecExecution.Eval.bind_success hchild
            exact SpecTecExecution.Eval.pure (SpecTec.strtype.DefStructT stp)
      | none =>
          have hchild : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.structtype,
                SpecTec.SpecTecCall.«$subst_structtype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» st⟩)
              start .unmatch start := by
            simpa [optionOutcome, hresult] using subst_structtype_of_total st dts start
          simp only [substStrtypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_strtype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefStructT st)) ())
            start .unmatch start
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_strtype:clause:0» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefStructT st))
              start .unmatch start
            unfold SpecTec.«$subst_strtype:clause:0»
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true
                (by simp [SpecTec.«exec:match:strtype:DefStructT»])
            · exact SpecTecExecution.Eval.bind_unmatch hchild
          · apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$subst_strtype:clause:1» (List SpecTec.deftype) dts
                  SpecTec.SpecTecCall.«$subst_of» (.DefStructT st)) start .unmatch start
              unfold SpecTec.«$subst_strtype:clause:1»
              apply SpecTecExecution.Eval.bind_unmatch
              exact SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
            · apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$subst_strtype:clause:2» (List SpecTec.deftype) dts
                    SpecTec.SpecTecCall.«$subst_of» (.DefStructT st)) start .unmatch start
                unfold SpecTec.«$subst_strtype:clause:2»
                apply SpecTecExecution.Eval.bind_unmatch
                exact SpecTecExecution.Eval.guard_false
                  (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
              · exact SpecTecExecution.firstSuccess_nil () start
  | DefArrayT arr =>
      cases hresult : substArraytypeResult arr dts with
      | some atp =>
          have hchild : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.arraytype,
                SpecTec.SpecTecCall.«$subst_arraytype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» arr⟩)
              start (.success (.of atp)) start := by
            simpa [optionOutcome, hresult] using subst_arraytype_of_total arr dts start
          simp only [substStrtypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_strtype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefArrayT arr)) ())
            start (.success (.of (SpecTec.strtype.DefArrayT atp))) start
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_strtype:clause:0» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefArrayT arr)) start .unmatch start
            unfold SpecTec.«$subst_strtype:clause:0»
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:strtype:DefStructT»])
          · apply SpecTecExecution.firstSuccess_cons_success
            change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_strtype:clause:1» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefArrayT arr))
              start (.success (.of (SpecTec.strtype.DefArrayT atp))) start
            unfold SpecTec.«$subst_strtype:clause:1»
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true
                (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
            · apply SpecTecExecution.Eval.bind_success hchild
              exact SpecTecExecution.Eval.pure (SpecTec.strtype.DefArrayT atp)
      | none =>
          have hchild : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.arraytype,
                SpecTec.SpecTecCall.«$subst_arraytype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» arr⟩)
              start .unmatch start := by
            simpa [optionOutcome, hresult] using subst_arraytype_of_total arr dts start
          simp only [substStrtypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_strtype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefArrayT arr)) ())
            start .unmatch start
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_strtype:clause:0» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefArrayT arr)) start .unmatch start
            unfold SpecTec.«$subst_strtype:clause:0»
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:strtype:DefStructT»])
          · apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$subst_strtype:clause:1» (List SpecTec.deftype) dts
                  SpecTec.SpecTecCall.«$subst_of» (.DefArrayT arr))
                start .unmatch start
              unfold SpecTec.«$subst_strtype:clause:1»
              apply SpecTecExecution.Eval.bind_success
              · exact SpecTecExecution.Eval.guard_true
                  (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
              · exact SpecTecExecution.Eval.bind_unmatch hchild
            · apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$subst_strtype:clause:2» (List SpecTec.deftype) dts
                    SpecTec.SpecTecCall.«$subst_of» (.DefArrayT arr)) start .unmatch start
                unfold SpecTec.«$subst_strtype:clause:2»
                apply SpecTecExecution.Eval.bind_unmatch
                exact SpecTecExecution.Eval.guard_false
                  (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
              · exact SpecTecExecution.firstSuccess_nil () start
  | DefFuncT ft =>
      cases hresult : substFunctypeResult ft dts with
      | some ftp =>
          have hchild : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.functype,
                SpecTec.SpecTecCall.«$subst_functype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» ft⟩)
              start (.success (.of ftp)) start := by
            simpa [optionOutcome, hresult] using subst_functype_of_total ft dts start
          simp only [substStrtypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_strtype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefFuncT ft)) ())
            start (.success (.of (SpecTec.strtype.DefFuncT ftp))) start
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_strtype:clause:0» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefFuncT ft)) start .unmatch start
            unfold SpecTec.«$subst_strtype:clause:0»
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:strtype:DefStructT»])
          · apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$subst_strtype:clause:1» (List SpecTec.deftype) dts
                  SpecTec.SpecTecCall.«$subst_of» (.DefFuncT ft)) start .unmatch start
              unfold SpecTec.«$subst_strtype:clause:1»
              apply SpecTecExecution.Eval.bind_unmatch
              exact SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
            · apply SpecTecExecution.firstSuccess_cons_success
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$subst_strtype:clause:2» (List SpecTec.deftype) dts
                  SpecTec.SpecTecCall.«$subst_of» (.DefFuncT ft))
                start (.success (.of (SpecTec.strtype.DefFuncT ftp))) start
              unfold SpecTec.«$subst_strtype:clause:2»
              apply SpecTecExecution.Eval.bind_success
              · exact SpecTecExecution.Eval.guard_true
                  (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
              · apply SpecTecExecution.Eval.bind_success hchild
                exact SpecTecExecution.Eval.pure (SpecTec.strtype.DefFuncT ftp)
      | none =>
          have hchild : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.functype,
                SpecTec.SpecTecCall.«$subst_functype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» ft⟩)
              start .unmatch start := by
            simpa [optionOutcome, hresult] using subst_functype_of_total ft dts start
          simp only [substStrtypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_strtype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefFuncT ft)) ())
            start .unmatch start
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_strtype:clause:0» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.DefFuncT ft)) start .unmatch start
            unfold SpecTec.«$subst_strtype:clause:0»
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:strtype:DefStructT»])
          · apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$subst_strtype:clause:1» (List SpecTec.deftype) dts
                  SpecTec.SpecTecCall.«$subst_of» (.DefFuncT ft)) start .unmatch start
              unfold SpecTec.«$subst_strtype:clause:1»
              apply SpecTecExecution.Eval.bind_unmatch
              exact SpecTecExecution.Eval.guard_false
                (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
            · apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$subst_strtype:clause:2» (List SpecTec.deftype) dts
                    SpecTec.SpecTecCall.«$subst_of» (.DefFuncT ft))
                  start .unmatch start
                unfold SpecTec.«$subst_strtype:clause:2»
                apply SpecTecExecution.Eval.bind_success
                · exact SpecTecExecution.Eval.guard_true
                    (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
                · exact SpecTecExecution.Eval.bind_unmatch hchild
              · exact SpecTecExecution.firstSuccess_nil () start

theorem subst_strtype_of_deterministic (st : SpecTec.strtype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype,
        SpecTec.SpecTecCall.«$subst_strtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» st⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substStrtypeResult st dts) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_strtype_of_total st dts start)

end properties.wasm_module_not_ok.Rejection
