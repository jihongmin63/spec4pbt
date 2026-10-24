import properties.wasm_module_not_ok.SubtypeSubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substSubtypeListResult (ts : List SpecTec.subtype)
    (dts : List SpecTec.deftype) : Option (List SpecTec.subtype) :=
  match ts with
  | [] => some []
  | t :: tail => do
      let t' ← substSubtypeResult t dts
      let tail' ← substSubtypeListResult tail dts
      pure (t' :: tail')

theorem subst_rectype_iter_of_total (ts : List SpecTec.subtype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.subtype,
        SpecTec.SpecTecCall.«$subst_rectype:case_1:iter:0»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» ts⟩)
      start (optionOutcome (substSubtypeListResult ts dts)) start := by
  induction ts with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_rectype:case_1:iter:0_clauses»
            (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» []) ())
        start (optionOutcome (substSubtypeListResult [] dts)) start
      simp only [substSubtypeListResult, optionOutcome]
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» [])
        start (.success (.of ([] : List SpecTec.subtype))) start
      simpa [SpecTec.«$subst_rectype:case_1:iter:0:clause:0»] using
        (SpecTecExecution.Eval.pure ([] : List SpecTec.subtype) (n := start))
  | cons t tail ih =>
      cases hhead : substSubtypeResult t dts with
      | none =>
          have hv : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.subtype,
                SpecTec.SpecTecCall.«$subst_subtype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» t⟩)
              start .unmatch start := by
            simpa [optionOutcome, hhead] using subst_subtype_of_total t dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_rectype:case_1:iter:0_clauses»
                (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» (t :: tail)) ())
            start (optionOutcome (substSubtypeListResult (t :: tail) dts)) start
          simp only [substSubtypeListResult, hhead, Option.bind, optionOutcome]
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
                (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» (t :: tail))
              start .unmatch start
            unfold SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
            exact SpecTecExecution.Eval.unmatch
          · apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$subst_rectype:case_1:iter:0:clause:1»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» (t :: tail))
                start .unmatch start
              unfold SpecTec.«$subst_rectype:case_1:iter:0:clause:1»
              exact SpecTecExecution.Eval.bind_unmatch hv
            · exact SpecTecExecution.firstSuccess_nil () start
      | some t' =>
          have hv : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.subtype,
                SpecTec.SpecTecCall.«$subst_subtype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» t⟩)
              start (.success (.of t')) start := by
            simpa [optionOutcome, hhead] using subst_subtype_of_total t dts start
          cases htail : substSubtypeListResult tail dts with
          | none =>
              have ht : SpecTecExecution.Eval SpecTec.specTecProgram
                  (.call ⟨List SpecTec.subtype,
                    SpecTec.SpecTecCall.«$subst_rectype:case_1:iter:0»
                      (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» tail⟩)
                  start .unmatch start := by
                simpa [optionOutcome, htail] using ih
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTecExecution.firstSuccess
                  (SpecTec.«$subst_rectype:case_1:iter:0_clauses»
                    (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                    (t :: tail)) ())
                start (optionOutcome (substSubtypeListResult (t :: tail) dts)) start
              simp only [substSubtypeListResult, hhead, Option.bind, htail, optionOutcome]
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
                    (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                    (t :: tail)) start .unmatch start
                unfold SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
                exact SpecTecExecution.Eval.unmatch
              · apply SpecTecExecution.firstSuccess_cons_unmatch
                · change SpecTecExecution.Eval SpecTec.specTecProgram
                    (SpecTec.«$subst_rectype:case_1:iter:0:clause:1»
                      (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                      (t :: tail)) start .unmatch start
                  unfold SpecTec.«$subst_rectype:case_1:iter:0:clause:1»
                  apply SpecTecExecution.Eval.bind_success hv
                  exact SpecTecExecution.Eval.bind_unmatch ht
                · exact SpecTecExecution.firstSuccess_nil () start
          | some tail' =>
              have ht : SpecTecExecution.Eval SpecTec.specTecProgram
                  (.call ⟨List SpecTec.subtype,
                    SpecTec.SpecTecCall.«$subst_rectype:case_1:iter:0»
                      (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» tail⟩)
                  start (.success (.of tail')) start := by
                simpa [optionOutcome, htail] using ih
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTecExecution.firstSuccess
                  (SpecTec.«$subst_rectype:case_1:iter:0_clauses»
                    (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                    (t :: tail)) ())
                start (optionOutcome (substSubtypeListResult (t :: tail) dts)) start
              simp [substSubtypeListResult, hhead, htail, optionOutcome]
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
                    (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                    (t :: tail)) start .unmatch start
                unfold SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
                exact SpecTecExecution.Eval.unmatch
              · apply SpecTecExecution.firstSuccess_cons_success
                change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$subst_rectype:case_1:iter:0:clause:1»
                    (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                    (t :: tail))
                  start (.success (.of (t' :: tail'))) start
                unfold SpecTec.«$subst_rectype:case_1:iter:0:clause:1»
                apply SpecTecExecution.Eval.bind_success hv
                apply SpecTecExecution.Eval.bind_success ht
                exact SpecTecExecution.Eval.pure (t' :: tail')


def substRectypeResult (st : SpecTec.rectype)
    (dts : List SpecTec.deftype) : Option SpecTec.rectype :=
  match st with
  | .RecT sts => (substSubtypeListResult sts dts).map SpecTec.rectype.RecT

theorem subst_rectype_of_total (st : SpecTec.rectype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.rectype,
        SpecTec.SpecTecCall.«$subst_rectype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» st⟩)
      start (optionOutcome (substRectypeResult st dts)) start := by
  cases st with
  | RecT sts =>
      cases hresult : substSubtypeListResult sts dts with
      | some sts' =>
          have hiter : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨List SpecTec.subtype,
                SpecTec.SpecTecCall.«$subst_rectype:case_1:iter:0»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» sts⟩)
              start (.success (.of sts')) start := by
            simpa [optionOutcome, hresult] using
              subst_rectype_iter_of_total sts dts start
          simp only [substRectypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_rectype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.RecT sts)) ())
            start (.success (.of (SpecTec.rectype.RecT sts'))) start
          apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_rectype:clause:0» (List SpecTec.deftype) dts
              SpecTec.SpecTecCall.«$subst_of» (.RecT sts))
            start (.success (.of (SpecTec.rectype.RecT sts'))) start
          unfold SpecTec.«$subst_rectype:clause:0»
          apply SpecTecExecution.Eval.bind_success hiter
          exact SpecTecExecution.Eval.pure (SpecTec.rectype.RecT sts')
      | none =>
          have hiter : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨List SpecTec.subtype,
                SpecTec.SpecTecCall.«$subst_rectype:case_1:iter:0»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» sts⟩)
              start .unmatch start := by
            simpa [optionOutcome, hresult] using
              subst_rectype_iter_of_total sts dts start
          simp only [substRectypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_rectype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.RecT sts)) ())
            start .unmatch start
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_rectype:clause:0» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.RecT sts)) start .unmatch start
            unfold SpecTec.«$subst_rectype:clause:0»
            exact SpecTecExecution.Eval.bind_unmatch hiter
          · exact SpecTecExecution.firstSuccess_nil () start

theorem subst_rectype_of_deterministic (st : SpecTec.rectype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.rectype,
        SpecTec.SpecTecCall.«$subst_rectype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» st⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substRectypeResult st dts) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_rectype_of_total st dts start)

end properties.wasm_module_not_ok.Rejection
