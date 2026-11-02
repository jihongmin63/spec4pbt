import properties.wasm_module_ok.ConstructiveBodyPopPlans
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyDispatch
open SpecTec properties.wasm_module_ok

theorem skip_head (head : SpecTecExecution.Action.{1} Request)
    (rest : List (SpecTecExecution.Action.{1} Request)) (start finish : Nat)
    (value : SpecTecExecution.Value) (h : SpecTecExecution.Eval SpecTec.Body
      (head ()) start .unmatch start) :
    SpecTecExecution.Eval SpecTec.Body (SpecTecExecution.tryClauses (head::rest))
      start (.success value) finish ↔
    SpecTecExecution.Eval SpecTec.Body (SpecTecExecution.tryClauses rest)
      start (.success value) finish := by
  constructor
  · intro hs
    cases hs with
    | orElse_success hs =>
      have hc := (properties.wasm_module_ok.Execution.eval_deterministic hs h).1
      cases hc
    | orElse_unmatch _ hs => exact hs
  · exact SpecTecExecution.tryClauses_cons_unmatch h

theorem keep_head (head : SpecTecExecution.Action.{1} Request)
    (rest : List (SpecTecExecution.Action.{1} Request)) (start finish : Nat)
    (value : SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses rest) start .unmatch start) :
    SpecTecExecution.Eval SpecTec.Body (SpecTecExecution.tryClauses (head::rest))
      start (.success value) finish ↔
    SpecTecExecution.Eval SpecTec.Body (head ()) start (.success value) finish := by
  constructor
  · intro hs
    cases hs with
    | orElse_success hs => exact hs
    | orElse_unmatch _ hs =>
      have hc := (properties.wasm_module_ok.Execution.eval_deterministic hs h).1
      cases hc
  · exact SpecTecExecution.tryClauses_cons_success

#print axioms skip_head
#print axioms keep_head
end properties.wasm_module_ok.ConstructiveBodyDispatch
