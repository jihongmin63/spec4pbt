import properties.wasm_module_not_ok.RectypeSubstOfValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substDeftypeResult (ft : SpecTec.deftype)
    (dts : List SpecTec.deftype) : Option SpecTec.deftype :=
  match ft with
  | .DefT rect n =>
      (substRectypeResult rect dts).map (fun rect' => SpecTec.deftype.DefT rect' n)

theorem subst_deftype_of_total (ft : SpecTec.deftype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.deftype,
        SpecTec.Call.«$subst_deftype»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ft⟩)
      start (optionOutcome (substDeftypeResult ft dts)) start := by
  cases ft with
  | DefT rect n =>
      cases hresult : substRectypeResult rect dts with
      | some rect' =>
          have hstorage : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨SpecTec.rectype,
                SpecTec.Call.«$subst_rectype»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» rect⟩)
              start (.success (.of rect')) start := by
            simpa [optionOutcome, hresult] using subst_rectype_of_total rect dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.«$subst_deftype_clauses» (List SpecTec.deftype) dts
                SpecTec.Call.«$subst_of» (.DefT rect n)))
            start (optionOutcome (substDeftypeResult (.DefT rect n) dts)) start
          simp only [substDeftypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.tryClauses_cons_success
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$subst_deftype:clause:0» (List SpecTec.deftype) dts
              SpecTec.Call.«$subst_of» (.DefT rect n))
            start (.success (.of (SpecTec.deftype.DefT rect' n))) start
          unfold SpecTec.«$subst_deftype:clause:0»
          apply SpecTecExecution.Eval.bind_success hstorage
          exact SpecTecExecution.Eval.pure (SpecTec.deftype.DefT rect' n)
      | none =>
          have hstorage : SpecTecExecution.Eval SpecTec.Body
              (.call ⟨SpecTec.rectype,
                SpecTec.Call.«$subst_rectype»
                  (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» rect⟩)
              start .unmatch start := by
            simpa [optionOutcome, hresult] using subst_rectype_of_total rect dts start
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.«$subst_deftype_clauses» (List SpecTec.deftype) dts
                SpecTec.Call.«$subst_of» (.DefT rect n)))
            start (optionOutcome (substDeftypeResult (.DefT rect n) dts)) start
          simp only [substDeftypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.tryClauses_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.Body
              (SpecTec.«$subst_deftype:clause:0» (List SpecTec.deftype) dts
                SpecTec.Call.«$subst_of» (.DefT rect n)) start .unmatch start
            unfold SpecTec.«$subst_deftype:clause:0»
            exact SpecTecExecution.Eval.bind_unmatch hstorage
          · exact SpecTecExecution.tryClauses_nil start

theorem subst_deftype_of_deterministic (ft : SpecTec.deftype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.deftype,
        SpecTec.Call.«$subst_deftype»
          (List SpecTec.deftype) dts SpecTec.Call.«$subst_of» ft⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substDeftypeResult ft dts) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_deftype_of_total ft dts start)

end properties.wasm_module_not_ok.Rejection
