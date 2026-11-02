import properties.wasm_module_not_ok.RectypeRollValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def rollDeftypes (x : Nat) (rect : SpecTec.rectype) :
    List SpecTec.deftype :=
  match rollRectypeAt x rect with
  | .RecT sts => rolledDefs (.RecT sts) 0 sts.length

theorem rolldt_total (x : Nat) (rect : SpecTec.rectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.deftype, SpecTec.Call.«$rolldt» x rect⟩)
      start (.success (.of (rollDeftypes x rect))) start := by
  cases rect with
  | RecT sts =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$rolldt_clauses» x (.RecT sts)))
        start (.success (.of (rollDeftypes x (.RecT sts)))) start
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$rolldt:clause:0» x (.RecT sts))
        start (.success (.of (rollDeftypes x (.RecT sts)))) start
      unfold SpecTec.«$rolldt:clause:0»
      apply SpecTecExecution.Eval.bind_success
        (rollrt_total x (.RecT sts) start)
      apply SpecTecExecution.Eval.bind_success
        (rolldt_aux_total
          (rollSubtypes sts x (sts.length + x)) 0 start)
      simpa [rollDeftypes, rollRectypeAt, rollRectype] using
        (SpecTecExecution.Eval.pure
          (rolledDefs
            (.RecT (rollSubtypes sts x (sts.length + x))) 0
            ((rollSubtypes sts x (sts.length + x)).length - 0))
          (n := start))

theorem rolldt_deterministic (x : Nat) (rect : SpecTec.rectype)
    (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨List SpecTec.deftype, SpecTec.Call.«$rolldt» x rect⟩)
      start outcome finalSupply) :
    outcome = .success (.of (rollDeftypes x rect)) ∧ finalSupply = start :=
  properties.wasm_module_ok.Execution.eval_deterministic h
    (rolldt_total x rect start)

end properties.wasm_module_not_ok.Rejection
