import properties.wasm_module_not_ok.ValtypeSubstOfValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substResulttypeResult (ts : List SpecTec.valtype)
    (dts : List SpecTec.deftype) : Option (List SpecTec.valtype) :=
  match ts with
  | [] => some []
  | t :: tail => do
      let t' ← substValtypeResult t dts
      let tail' ← substResulttypeResult tail dts
      pure (t' :: tail')

theorem subst_resulttype_iter_of_total (ts : List SpecTec.valtype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.valtype,
        SpecTec.Call.«$subst_resulttype:case_1:iter:0»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ts⟩)
      start (optionOutcome (substResulttypeResult ts dts)) start := by
  induction ts with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_resulttype:case_1:iter:0_clauses»
            (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» []))
        start (optionOutcome (substResulttypeResult [] dts)) start
      simp only [substResulttypeResult, optionOutcome]
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» [])
        start (.success (.of ([] : List SpecTec.valtype))) start
      simpa [SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»] using
        (SpecTecExecution.Eval.pure ([] : List SpecTec.valtype) (n := start))
  | cons t tail ih =>
      cases hhead : substValtypeResult t dts with
      | none =>
          have hv : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨SpecTec.valtype,
                SpecTec.Call.«$subst_valtype»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» t⟩)
              start .unmatch start := by
            simpa [optionOutcome, hhead] using subst_valtype_of_total t dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.«$subst_resulttype:case_1:iter:0_clauses»
                (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» (t :: tail)))
            start (optionOutcome (substResulttypeResult (t :: tail) dts)) start
          simp only [substResulttypeResult, hhead, Option.bind, optionOutcome]
          apply SpecTecExecution.tryClauses_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»
                (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» (t :: tail))
              start .unmatch start
            unfold SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»
            exact SpecTecExecution.Eval.unmatch
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.Body
                (SpecTec.«$subst_resulttype:case_1:iter:0:clause:1»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» (t :: tail))
                start .unmatch start
              unfold SpecTec.«$subst_resulttype:case_1:iter:0:clause:1»
              exact SpecTecExecution.Eval.bind_unmatch hv
            · exact SpecTecExecution.tryClauses_nil start
      | some t' =>
          have hv : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨SpecTec.valtype,
                SpecTec.Call.«$subst_valtype»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» t⟩)
              start (.success (.of t')) start := by
            simpa [optionOutcome, hhead] using subst_valtype_of_total t dts start
          cases htail : substResulttypeResult tail dts with
          | none =>
              have ht : SpecTecExecution.Eval SpecTec.Body
                  (.call ⟨List SpecTec.valtype,
                    SpecTec.Call.«$subst_resulttype:case_1:iter:0»
                      (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» tail⟩)
                  start .unmatch start := by
                simpa [optionOutcome, htail] using ih
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.Body
                (SpecTecExecution.tryClauses
                  (SpecTec.«$subst_resulttype:case_1:iter:0_clauses»
                    (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                    (t :: tail)))
                start (optionOutcome (substResulttypeResult (t :: tail) dts)) start
              simp only [substResulttypeResult, hhead, Option.bind, htail, optionOutcome]
              apply SpecTecExecution.tryClauses_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.Body
                  (SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»
                    (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                    (t :: tail)) start .unmatch start
                unfold SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»
                exact SpecTecExecution.Eval.unmatch
              · apply SpecTecExecution.tryClauses_cons_unmatch
                · change SpecTecExecution.Eval SpecTec.Body
                    (SpecTec.«$subst_resulttype:case_1:iter:0:clause:1»
                      (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                      (t :: tail)) start .unmatch start
                  unfold SpecTec.«$subst_resulttype:case_1:iter:0:clause:1»
                  apply SpecTecExecution.Eval.bind_success hv
                  exact SpecTecExecution.Eval.bind_unmatch ht
                · exact SpecTecExecution.tryClauses_nil start
          | some tail' =>
              have ht : SpecTecExecution.Eval SpecTec.Body
                  (.call ⟨List SpecTec.valtype,
                    SpecTec.Call.«$subst_resulttype:case_1:iter:0»
                      (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» tail⟩)
                  start (.success (.of tail')) start := by
                simpa [optionOutcome, htail] using ih
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.Body
                (SpecTecExecution.tryClauses
                  (SpecTec.«$subst_resulttype:case_1:iter:0_clauses»
                    (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                    (t :: tail)))
                start (optionOutcome (substResulttypeResult (t :: tail) dts)) start
              simp [substResulttypeResult, hhead, htail, optionOutcome]
              apply SpecTecExecution.tryClauses_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.Body
                  (SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»
                    (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                    (t :: tail)) start .unmatch start
                unfold SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»
                exact SpecTecExecution.Eval.unmatch
              · apply SpecTecExecution.tryClauses_cons_success
                change SpecTecExecution.Eval SpecTec.Body
                  (SpecTec.«$subst_resulttype:case_1:iter:0:clause:1»
                    (List SpecTec.deftype) dts SpecTec.Call.«$subst_of»
                    (t :: tail))
                  start (.success (.of (t' :: tail'))) start
                unfold SpecTec.«$subst_resulttype:case_1:iter:0:clause:1»
                apply SpecTecExecution.Eval.bind_success hv
                apply SpecTecExecution.Eval.bind_success ht
                exact SpecTecExecution.Eval.pure (t' :: tail')

theorem subst_resulttype_of_total (ts : SpecTec.resulttype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.resulttype,
        SpecTec.Call.«$subst_resulttype»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ts⟩)
      start (optionOutcome (substResulttypeResult ts dts)) start := by
  cases hresult : substResulttypeResult ts dts with
  | some ts' =>
      have hiter : SpecTecExecution.Eval SpecTec.Body
          (.call ⟨List SpecTec.valtype,
            SpecTec.Call.«$subst_resulttype:case_1:iter:0»
              (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ts⟩)
          start (.success (.of ts')) start := by
        simpa [optionOutcome, hresult] using
          subst_resulttype_iter_of_total ts dts start
      simp only [hresult, optionOutcome]
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_resulttype_clauses» (List SpecTec.deftype) dts
            SpecTec.Call.«$subst_of» ts))
        start (.success (.of ts')) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$subst_resulttype:clause:0» (List SpecTec.deftype) dts
          SpecTec.Call.«$subst_of» ts)
        start (.success (.of ts')) start
      unfold SpecTec.«$subst_resulttype:clause:0»
      apply SpecTecExecution.Eval.bind_success hiter
      exact SpecTecExecution.Eval.pure ts'
  | none =>
      have hiter : SpecTecExecution.Eval SpecTec.Body
          (.call ⟨List SpecTec.valtype,
            SpecTec.Call.«$subst_resulttype:case_1:iter:0»
              (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ts⟩)
          start .unmatch start := by
        simpa [optionOutcome, hresult] using
          subst_resulttype_iter_of_total ts dts start
      simp only [hresult, optionOutcome]
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$subst_resulttype_clauses» (List SpecTec.deftype) dts
            SpecTec.Call.«$subst_of» ts))
        start .unmatch start
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$subst_resulttype:clause:0» (List SpecTec.deftype) dts
            SpecTec.Call.«$subst_of» ts) start .unmatch start
        unfold SpecTec.«$subst_resulttype:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch hiter
      · exact SpecTecExecution.tryClauses_nil start

theorem subst_resulttype_of_deterministic (ts : SpecTec.resulttype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.resulttype,
        SpecTec.Call.«$subst_resulttype»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ts⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substResulttypeResult ts dts) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_resulttype_of_total ts dts start)

end properties.wasm_module_not_ok.Rejection
