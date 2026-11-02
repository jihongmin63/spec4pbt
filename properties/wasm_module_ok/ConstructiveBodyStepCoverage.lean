import properties.wasm_module_ok.ConstructiveBodyProductionCoverage
import properties.wasm_module_ok.ConstructiveBodyEvalReduction
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyStepCoverage
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyProductionCoverage ConstructiveConstTableCore

/-- Invert one original transition against a production that actually emits its
instruction. The next environment is derived by that production, not assumed. -/
theorem original (c : context) (stack : inferresulttype) (env : Env c)
    (hs : StackBacked c stack) (ps : List (Production c stack)) (i : instr) (effect : inferinstrtype)
    (nextContext : context) (popped nextStack : inferresulttype) (n n1 n2 n3 n4 : Nat)
    (hc : Covers ps i effect)
    (hi : Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack i⟩) n (.success (.of effect)) n1)
    (hl : Eval SpecTec.Body (.call ⟨context,Call.«$init_locals» c effect.2⟩) n1 (.success (.of nextContext)) n2)
    (hp : Eval SpecTec.Body (.call ⟨inferresulttype,Call.«$pop» c effect.1.INS stack⟩) n2 (.success (.of popped)) n3)
    (hq : Eval SpecTec.Body (.call ⟨inferresulttype,Call.«$push» c effect.1.OUTS popped⟩) n3 (.success (.of nextStack)) n4) :
    ∃p∈ps,∃g s,prepare c stack env hs p=some g ∧ Gen.support g.generator s ∧
      s.instruction=i ∧ s.nextContext=nextContext ∧ s.nextStack=nextStack ∧ n4=n := by
  obtain ⟨p,hpMem,heff,v,hv,hiv⟩ := hc
  subst effect
  have hi' := v.property n
  rw [hiv] at hi'
  have hn1 := (properties.wasm_module_ok.Execution.eval_deterministic hi hi').2
  subst n1
  obtain ⟨hctx,hn2⟩ := properties.wasm_module_ok.Execution.eval_deterministic hl (p.initialized n)
  have hctx : nextContext=p.nextContext := by cases hctx; rfl
  subst nextContext
  subst n2
  obtain ⟨hpPlan,hn3⟩ := ConstructiveBodyPopPlans.pop_plan_complete c p.effect.1.INS stack popped n n3 env.ready p.inputsBacked hs hp
  subst n3
  obtain ⟨hqPlan,hn4⟩ := (PushValidation.push_success_iff_result c p.effect.1.OUTS popped nextStack n n4).1 hq
  let s := step c stack env hs p popped nextStack hpPlan hqPlan v
  let g := p.instructions.map (step c stack env hs p popped nextStack hpPlan hqPlan)
  refine ⟨p,hpMem,g,s,?_,?_,hiv,rfl,rfl,hn4⟩
  · unfold prepare
    split
    next hnone => rw [hpPlan] at hnone; cases hnone
    next popped' hp' =>
      have he : popped'=popped := Option.some.inj (hp'.symm.trans hpPlan)
      subst popped'
      split
      next hnone => rw [hqPlan] at hnone; cases hnone
      next next' hq' =>
        have he : next'=nextStack := Option.some.inj (hq'.symm.trans hqPlan)
        subst next'
        rfl
  · exact ⟨v,hv,rfl⟩

#print axioms original
end properties.wasm_module_ok.ConstructiveBodyStepCoverage
