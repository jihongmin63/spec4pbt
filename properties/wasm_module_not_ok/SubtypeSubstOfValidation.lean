import properties.wasm_module_not_ok.HeaptypeSubstOfValidation
import properties.wasm_module_not_ok.StrtypeSubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substHeaptypeListResult (ts : List SpecTec.heaptype)
    (dts : List SpecTec.deftype) : Option (List SpecTec.heaptype) :=
  match ts with
  | [] => some []
  | t :: tail => do
      let t' ← substHeaptypeResult t dts
      let tail' ← substHeaptypeListResult tail dts
      pure (t' :: tail')

theorem subst_subtype_iter_of_total (ts : List SpecTec.heaptype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.heaptype,
        SpecTec.SpecTecCall.«$subst_subtype:case_1:iter:0»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» ts⟩)
      start (optionOutcome (substHeaptypeListResult ts dts)) start := by
  induction ts with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_subtype:case_1:iter:0_clauses»
            (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» []) ())
        start (optionOutcome (substHeaptypeListResult [] dts)) start
      simp only [substHeaptypeListResult, optionOutcome]
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» [])
        start (.success (.of ([] : List SpecTec.heaptype))) start
      simpa [SpecTec.«$subst_subtype:case_1:iter:0:clause:0»] using
        (SpecTecExecution.Eval.pure ([] : List SpecTec.heaptype) (n := start))
  | cons t tail ih =>
      cases hhead : substHeaptypeResult t dts with
      | none =>
          have hv : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.heaptype,
                SpecTec.SpecTecCall.«$subst_heaptype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» t⟩)
              start .unmatch start := by
            simpa [optionOutcome, hhead] using subst_heaptype_of_total t dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_subtype:case_1:iter:0_clauses»
                (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» (t :: tail)) ())
            start (optionOutcome (substHeaptypeListResult (t :: tail) dts)) start
          simp only [substHeaptypeListResult, hhead, Option.bind, optionOutcome]
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
                (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» (t :: tail))
              start .unmatch start
            unfold SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
            exact SpecTecExecution.Eval.unmatch
          · apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$subst_subtype:case_1:iter:0:clause:1»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» (t :: tail))
                start .unmatch start
              unfold SpecTec.«$subst_subtype:case_1:iter:0:clause:1»
              exact SpecTecExecution.Eval.bind_unmatch hv
            · exact SpecTecExecution.firstSuccess_nil () start
      | some t' =>
          have hv : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.heaptype,
                SpecTec.SpecTecCall.«$subst_heaptype»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» t⟩)
              start (.success (.of t')) start := by
            simpa [optionOutcome, hhead] using subst_heaptype_of_total t dts start
          cases htail : substHeaptypeListResult tail dts with
          | none =>
              have ht : SpecTecExecution.Eval SpecTec.specTecProgram
                  (.call ⟨List SpecTec.heaptype,
                    SpecTec.SpecTecCall.«$subst_subtype:case_1:iter:0»
                      (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» tail⟩)
                  start .unmatch start := by
                simpa [optionOutcome, htail] using ih
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTecExecution.firstSuccess
                  (SpecTec.«$subst_subtype:case_1:iter:0_clauses»
                    (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                    (t :: tail)) ())
                start (optionOutcome (substHeaptypeListResult (t :: tail) dts)) start
              simp only [substHeaptypeListResult, hhead, Option.bind, htail, optionOutcome]
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
                    (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                    (t :: tail)) start .unmatch start
                unfold SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
                exact SpecTecExecution.Eval.unmatch
              · apply SpecTecExecution.firstSuccess_cons_unmatch
                · change SpecTecExecution.Eval SpecTec.specTecProgram
                    (SpecTec.«$subst_subtype:case_1:iter:0:clause:1»
                      (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                      (t :: tail)) start .unmatch start
                  unfold SpecTec.«$subst_subtype:case_1:iter:0:clause:1»
                  apply SpecTecExecution.Eval.bind_success hv
                  exact SpecTecExecution.Eval.bind_unmatch ht
                · exact SpecTecExecution.firstSuccess_nil () start
          | some tail' =>
              have ht : SpecTecExecution.Eval SpecTec.specTecProgram
                  (.call ⟨List SpecTec.heaptype,
                    SpecTec.SpecTecCall.«$subst_subtype:case_1:iter:0»
                      (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» tail⟩)
                  start (.success (.of tail')) start := by
                simpa [optionOutcome, htail] using ih
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTecExecution.firstSuccess
                  (SpecTec.«$subst_subtype:case_1:iter:0_clauses»
                    (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                    (t :: tail)) ())
                start (optionOutcome (substHeaptypeListResult (t :: tail) dts)) start
              simp [substHeaptypeListResult, hhead, htail, optionOutcome]
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
                    (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                    (t :: tail)) start .unmatch start
                unfold SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
                exact SpecTecExecution.Eval.unmatch
              · apply SpecTecExecution.firstSuccess_cons_success
                change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$subst_subtype:case_1:iter:0:clause:1»
                    (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of»
                    (t :: tail))
                  start (.success (.of (t' :: tail'))) start
                unfold SpecTec.«$subst_subtype:case_1:iter:0:clause:1»
                apply SpecTecExecution.Eval.bind_success hv
                apply SpecTecExecution.Eval.bind_success ht
                exact SpecTecExecution.Eval.pure (t' :: tail')


def substSubtypeResult (ft : SpecTec.subtype)
    (dts : List SpecTec.deftype) : Option SpecTec.subtype :=
  match ft with
  | .SubT fin hts strt => do
      let hts' ← substHeaptypeListResult hts dts
      let strt' ← substStrtypeResult strt dts
      pure (.SubT fin hts' strt')

theorem subst_subtype_of_total (ft : SpecTec.subtype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.subtype,
        SpecTec.SpecTecCall.«$subst_subtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» ft⟩)
      start (optionOutcome (substSubtypeResult ft dts)) start := by
  cases ft with
  | SubT fin hts strt =>
      cases hins : substHeaptypeListResult hts dts with
      | none =>
          have hfirst : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨List SpecTec.heaptype,
                SpecTec.SpecTecCall.«$subst_subtype:case_1:iter:0»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» hts⟩)
              start .unmatch start := by
            simpa [optionOutcome, hins] using subst_subtype_iter_of_total hts dts start
          simp only [substSubtypeResult, hins, Option.bind, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«$subst_subtype_clauses» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.SubT fin hts strt)) ())
            start .unmatch start
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_subtype:clause:0» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.SubT fin hts strt))
              start .unmatch start
            unfold SpecTec.«$subst_subtype:clause:0»
            exact SpecTecExecution.Eval.bind_unmatch hfirst
          · exact SpecTecExecution.firstSuccess_nil () start
      | some hts' =>
          have hfirst : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨List SpecTec.heaptype,
                SpecTec.SpecTecCall.«$subst_subtype:case_1:iter:0»
                  (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» hts⟩)
              start (.success (.of hts')) start := by
            simpa [optionOutcome, hins] using subst_subtype_iter_of_total hts dts start
          cases houts : substStrtypeResult strt dts with
          | none =>
              have hsecond : SpecTecExecution.Eval SpecTec.specTecProgram
                  (.call ⟨SpecTec.strtype,
                    SpecTec.SpecTecCall.«$subst_strtype»
                      (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» strt⟩)
                  start .unmatch start := by
                simpa [optionOutcome, houts] using
                  subst_strtype_of_total strt dts start
              simp only [substSubtypeResult, hins, houts, Option.bind, optionOutcome]
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTecExecution.firstSuccess
                  (SpecTec.«$subst_subtype_clauses» (List SpecTec.deftype) dts
                    SpecTec.SpecTecCall.«$subst_of» (.SubT fin hts strt)) ())
                start .unmatch start
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.specTecProgram
                  (SpecTec.«$subst_subtype:clause:0» (List SpecTec.deftype) dts
                    SpecTec.SpecTecCall.«$subst_of» (.SubT fin hts strt))
                  start .unmatch start
                unfold SpecTec.«$subst_subtype:clause:0»
                apply SpecTecExecution.Eval.bind_success hfirst
                exact SpecTecExecution.Eval.bind_unmatch hsecond
              · exact SpecTecExecution.firstSuccess_nil () start
          | some strt' =>
              have hsecond : SpecTecExecution.Eval SpecTec.specTecProgram
                  (.call ⟨SpecTec.strtype,
                    SpecTec.SpecTecCall.«$subst_strtype»
                      (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» strt⟩)
                  start (.success (.of strt')) start := by
                simpa [optionOutcome, houts] using
                  subst_strtype_of_total strt dts start
              simp only [substSubtypeResult, hins, houts, Option.bind, optionOutcome]
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTecExecution.firstSuccess
                  (SpecTec.«$subst_subtype_clauses» (List SpecTec.deftype) dts
                    SpecTec.SpecTecCall.«$subst_of» (.SubT fin hts strt)) ())
                start (.success (.of (SpecTec.subtype.SubT fin hts' strt'))) start
              apply SpecTecExecution.firstSuccess_cons_success
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$subst_subtype:clause:0» (List SpecTec.deftype) dts
                  SpecTec.SpecTecCall.«$subst_of» (.SubT fin hts strt))
                start (.success (.of (SpecTec.subtype.SubT fin hts' strt'))) start
              unfold SpecTec.«$subst_subtype:clause:0»
              apply SpecTecExecution.Eval.bind_success hfirst
              apply SpecTecExecution.Eval.bind_success hsecond
              exact SpecTecExecution.Eval.pure (SpecTec.subtype.SubT fin hts' strt')

theorem subst_subtype_of_deterministic (ft : SpecTec.subtype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.subtype,
        SpecTec.SpecTecCall.«$subst_subtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» ft⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substSubtypeResult ft dts) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_subtype_of_total ft dts start)

end properties.wasm_module_not_ok.Rejection
