import properties.wasm_module_not_ok.ResulttypeSubstOfValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substFunctypeResult (ft : SpecTec.functype)
    (dts : List SpecTec.deftype) : Option SpecTec.functype :=
  match ft with
  | .FuncT ins outs => do
      let ins' ← substResulttypeResult ins dts
      let outs' ← substResulttypeResult outs dts
      pure (.FuncT ins' outs')

theorem subst_functype_of_total (ft : SpecTec.functype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.functype,
        SpecTec.Call.«$subst_functype»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ft⟩)
      start (optionOutcome (substFunctypeResult ft dts)) start := by
  cases ft with
  | FuncT ins outs =>
      cases hins : substResulttypeResult ins dts with
      | none =>
          have hfirst : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨SpecTec.resulttype,
                SpecTec.Call.«$subst_resulttype»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ins⟩)
              start .unmatch start := by
            simpa [optionOutcome, hins] using subst_resulttype_of_total ins dts start
          simp only [substFunctypeResult, hins, Option.bind, optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.«$subst_functype_clauses» (List SpecTec.deftype) dts
                SpecTec.Call.«$subst_of» (.FuncT ins outs)))
            start .unmatch start
          apply SpecTecExecution.tryClauses_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«$subst_functype:clause:0» (List SpecTec.deftype) dts
                SpecTec.Call.«$subst_of» (.FuncT ins outs))
              start .unmatch start
            unfold SpecTec.«$subst_functype:clause:0»
            exact SpecTecExecution.Eval.bind_unmatch hfirst
          · exact SpecTecExecution.tryClauses_nil start
      | some ins' =>
          have hfirst : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨SpecTec.resulttype,
                SpecTec.Call.«$subst_resulttype»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ins⟩)
              start (.success (.of ins')) start := by
            simpa [optionOutcome, hins] using subst_resulttype_of_total ins dts start
          cases houts : substResulttypeResult outs dts with
          | none =>
              have hsecond : SpecTecExecution.Eval SpecTec.Body
                  (.call ⟨SpecTec.resulttype,
                    SpecTec.Call.«$subst_resulttype»
                      (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» outs⟩)
                  start .unmatch start := by
                simpa [optionOutcome, houts] using
                  subst_resulttype_of_total outs dts start
              simp only [substFunctypeResult, hins, houts, Option.bind, optionOutcome]
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.Body
                (SpecTecExecution.tryClauses
                  (SpecTec.«$subst_functype_clauses» (List SpecTec.deftype) dts
                    SpecTec.Call.«$subst_of» (.FuncT ins outs)))
                start .unmatch start
              apply SpecTecExecution.tryClauses_cons_unmatch
              · change SpecTecExecution.Eval SpecTec.Body
                  (SpecTec.«$subst_functype:clause:0» (List SpecTec.deftype) dts
                    SpecTec.Call.«$subst_of» (.FuncT ins outs))
                  start .unmatch start
                unfold SpecTec.«$subst_functype:clause:0»
                apply SpecTecExecution.Eval.bind_success hfirst
                exact SpecTecExecution.Eval.bind_unmatch hsecond
              · exact SpecTecExecution.tryClauses_nil start
          | some outs' =>
              have hsecond : SpecTecExecution.Eval SpecTec.Body
                  (.call ⟨SpecTec.resulttype,
                    SpecTec.Call.«$subst_resulttype»
                      (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» outs⟩)
                  start (.success (.of outs')) start := by
                simpa [optionOutcome, houts] using
                  subst_resulttype_of_total outs dts start
              simp only [substFunctypeResult, hins, houts, Option.bind, optionOutcome]
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.Body
                (SpecTecExecution.tryClauses
                  (SpecTec.«$subst_functype_clauses» (List SpecTec.deftype) dts
                    SpecTec.Call.«$subst_of» (.FuncT ins outs)))
                start (.success (.of (SpecTec.functype.FuncT ins' outs'))) start
              apply SpecTecExecution.tryClauses_cons_success
              change SpecTecExecution.Eval SpecTec.Body
                (SpecTec.«$subst_functype:clause:0» (List SpecTec.deftype) dts
                  SpecTec.Call.«$subst_of» (.FuncT ins outs))
                start (.success (.of (SpecTec.functype.FuncT ins' outs'))) start
              unfold SpecTec.«$subst_functype:clause:0»
              apply SpecTecExecution.Eval.bind_success hfirst
              apply SpecTecExecution.Eval.bind_success hsecond
              exact SpecTecExecution.Eval.pure (SpecTec.functype.FuncT ins' outs')

theorem subst_functype_of_deterministic (ft : SpecTec.functype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.functype,
        SpecTec.Call.«$subst_functype»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ft⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substFunctypeResult ft dts) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_functype_of_total ft dts start)

end properties.wasm_module_not_ok.Rejection
