import properties.wasm_module_ok.ConstructiveBodyPopPlans
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyDispatch
open SpecTec properties.wasm_module_ok
private theorem deterministic : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
  intro request a b h; cases h

theorem skip_head (head : SpecTecExecution.Clause SpecTecRequest Unit)
    (rest : List (SpecTecExecution.Clause SpecTecRequest Unit)) (start finish : Nat)
    (value : SpecTecExecution.Value) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (head ()) start .unmatch start) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTecExecution.firstSuccess (head::rest) ())
      start (.success value) finish ↔
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTecExecution.firstSuccess rest ())
      start (.success value) finish := by
  constructor
  · intro hs
    cases hs with
    | orElse_success hs =>
      have hc := (SpecTecExecution.eval_deterministic deterministic hs h).1
      cases hc
    | orElse_unmatch _ hs => exact hs
  · exact SpecTecExecution.firstSuccess_cons_unmatch h

theorem keep_head (head : SpecTecExecution.Clause SpecTecRequest Unit)
    (rest : List (SpecTecExecution.Clause SpecTecRequest Unit)) (start finish : Nat)
    (value : SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess rest ()) start .unmatch start) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTecExecution.firstSuccess (head::rest) ())
      start (.success value) finish ↔
    SpecTecExecution.Eval SpecTec.specTecProgram (head ()) start (.success value) finish := by
  constructor
  · intro hs
    cases hs with
    | orElse_success hs => exact hs
    | orElse_unmatch _ hs =>
      have hc := (SpecTecExecution.eval_deterministic deterministic hs h).1
      cases hc
  · exact SpecTecExecution.firstSuccess_cons_success

#print axioms skip_head
#print axioms keep_head
end properties.wasm_module_ok.ConstructiveBodyDispatch
