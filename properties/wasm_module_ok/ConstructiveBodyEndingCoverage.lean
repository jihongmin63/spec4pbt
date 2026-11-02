import properties.wasm_module_ok.ConstructiveBodyTail
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyEndingCoverage
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveBodyTail ConstructiveConstTableCore

theorem stop_supported (root c : context) (stack : inferresulttype) (outputs : List valtype)
    (env : Env root) (hs : StackBacked root stack)
    (ho : ∀t∈outputs,CandidateValMatch.InTableVal root t) (ell : ellipses)
    (hp : ConstructiveBodyPopPlans.popPlan root (.NoEllipses,outputs) stack=some (ell,[])) :
    ∃tail,Gen.support (endings root c stack outputs env hs ho).generator tail ∧ tail.val=[] := by
  unfold endings
  split
  next ell' he =>
    exact ⟨_,Or.inl rfl,rfl⟩
  next hbad =>
    exact False.elim (hbad ell hp)

theorem original (root c : context) (stack : inferresulttype) (outputs : List valtype)
    (env : Env root) (hs : StackBacked root stack)
    (ho : ∀t∈outputs,CandidateValMatch.InTableVal root t) (ell : ellipses) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferresulttype,SpecTecCall.«$pop» root (.NoEllipses,outputs) stack⟩)
      n (.success (.of ((ell,[]) : inferresulttype))) finish) :
    (∃tail,Gen.support (endings root c stack outputs env hs ho).generator tail ∧ tail.val=[]) ∧ finish=n := by
  obtain ⟨hp,hn⟩ := ConstructiveBodyPopPlans.pop_plan_complete root (.NoEllipses,outputs) stack (ell,[]) n finish env.ready ho hs h
  exact ⟨stop_supported root c stack outputs env hs ho ell hp,hn⟩

#print axioms original
end properties.wasm_module_ok.ConstructiveBodyEndingCoverage
