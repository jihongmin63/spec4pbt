import properties.wasm_module_not_ok.SubstOfValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def optionOutcome {α : Type} (result : Option α) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match result with
  | some value => .success (.of value)
  | none => .unmatch

def substOfResult (tv : SpecTec.typevar)
    (dts : List SpecTec.deftype) : Option SpecTec.heaptype :=
  match tv with
  | .StatX n => (dts[n]?).map SpecTec.heaptype.DefHT
  | .RecX n => some (.VarHT (.RecX n))

theorem subst_of_total_result (tv : SpecTec.typevar)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_of» tv dts⟩)
      start (optionOutcome (substOfResult tv dts)) start := by
  cases tv with
  | RecX n =>
      simpa [substOfResult, optionOutcome, substOfOutcome] using
        subst_of_total (.RecX n) dts start
  | StatX n =>
      cases hget : dts[n]? with
      | none =>
          simpa [substOfResult, optionOutcome, substOfOutcome, hget] using
            subst_of_total (.StatX n) dts start
      | some dt =>
          simpa [substOfResult, optionOutcome, substOfOutcome, hget] using
            subst_of_total (.StatX n) dts start

theorem subst_of_deterministic_result (tv : SpecTec.typevar)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype,
        SpecTec.Call.«$subst_of» tv dts⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substOfResult tv dts) ∧
      finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (subst_of_total_result tv dts start)

end properties.wasm_module_not_ok.Rejection
