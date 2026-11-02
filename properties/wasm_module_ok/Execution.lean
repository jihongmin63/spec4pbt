import Lean
import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.Execution

/-- A plan that reaches neither `choose` nor `freshId`. The Wasm specification uses neither. -/
def Plain : SpecTecExecution.Action.{1} SpecTec.Request → Prop
  | .pure _ => True
  | .unmatch => True
  | .abort _ => True
  | .freshId => False
  | .call _ => True
  | .choose _ _ => False
  | .guard _ => True
  | .bind plan next => Plain plan ∧ ∀ value, Plain (next value)
  | .orElse plan next => Plain plan ∧ Plain (next ())
  | .notHold plan => Plain plan

open Lean Meta Elab Tactic in
/-- Prove `Plain` for a specification plan by unfolding it and splitting its matches.
Goals are kept on a worklist so deep plans do not nest tactic calls. -/
elab "wasm_plain" : tactic => do
  let mut work := ← getGoals
  while true do
    let goal :: rest := work | break
    work := rest
    let (target, goal) ← goal.withContext do
      let target ← instantiateMVars (← goal.getType)
      let target ← match target.app1? ``Plain with
        | some plan => whnfD (mkApp target.appFn! (← whnfD plan))
        | none => whnfD target
      return (target, ← goal.replaceTargetDefEq target)
    if target.isConstOf ``True then
      goal.assign (mkConst ``True.intro)
    else if target.isAppOfArity ``And 2 then
      work := (← goal.constructor) ++ work
    else if target.isForall then
      work := (← goal.intro1).2 :: work
    else
      setGoals [goal]
      evalTactic (← `(tactic| split))
      work := (← getGoals) ++ work
  setGoals []

theorem body_plain (request : SpecTec.Request) : Plain (SpecTec.Body request) := by
  obtain ⟨_, call⟩ := request
  cases call <;> wasm_plain

/-- Without `choose` or `freshId`, every derivation is functional and keeps its supply. -/
theorem eval_plain {plan : SpecTecExecution.Action.{1} SpecTec.Request}
    {start final : Nat} {outcome : SpecTecExecution.Outcome SpecTecExecution.Value}
    (h : SpecTecExecution.Eval SpecTec.Body plan start outcome final) (plain : Plain plan) :
    SpecTecExecution.Functional SpecTec.Body h ∧ final = start := by
  induction h with
  | pure value => exact ⟨.pure value, rfl⟩
  | unmatch => exact ⟨.unmatch, rfl⟩
  | abort message => exact ⟨.abort message, rfl⟩
  | freshId => exact False.elim plain
  | call _ ih =>
    obtain ⟨functional, supply⟩ := ih (body_plain _)
    exact ⟨.call functional, supply⟩
  | choose => exact False.elim plain
  | guard_true h => exact ⟨.guard_true (h := h), rfl⟩
  | guard_false h => exact ⟨.guard_false (h := h), rfl⟩
  | bind_success _ _ first second =>
    obtain ⟨f₁, s₁⟩ := first plain.1
    obtain ⟨f₂, s₂⟩ := second (plain.2 _)
    exact ⟨.bind_success f₁ f₂, s₂.trans s₁⟩
  | bind_unmatch _ first =>
    obtain ⟨f, s⟩ := first plain.1
    exact ⟨.bind_unmatch f, s⟩
  | bind_abort _ first =>
    obtain ⟨f, s⟩ := first plain.1
    exact ⟨.bind_abort f, s⟩
  | orElse_success _ first =>
    obtain ⟨f, s⟩ := first plain.1
    exact ⟨.orElse_success f, s⟩
  | orElse_unmatch _ _ first second =>
    obtain ⟨f₁, s₁⟩ := first plain.1
    obtain ⟨f₂, s₂⟩ := second plain.2
    exact ⟨.orElse_unmatch f₁ f₂, s₂.trans s₁⟩
  | orElse_abort _ first =>
    obtain ⟨f, s⟩ := first plain.1
    exact ⟨.orElse_abort f, s⟩
  | notHold_success _ first =>
    obtain ⟨f, s⟩ := first plain
    exact ⟨.notHold_success f, s⟩
  | notHold_unmatch _ first =>
    obtain ⟨f, s⟩ := first plain
    exact ⟨.notHold_unmatch f, s⟩
  | notHold_abort _ first =>
    obtain ⟨f, s⟩ := first plain
    exact ⟨.notHold_abort f, s⟩

theorem eval_supply {plan : SpecTecExecution.Action.{1} SpecTec.Request}
    {start final : Nat} {outcome : SpecTecExecution.Outcome SpecTecExecution.Value}
    (h : SpecTecExecution.Eval SpecTec.Body plan start outcome final)
    (plain : Plain plan := by wasm_plain) : final = start :=
  (eval_plain h plain).2

theorem eval_deterministic {plan : SpecTecExecution.Action.{1} SpecTec.Request}
    {start leftFinal rightFinal : Nat}
    {left right : SpecTecExecution.Outcome SpecTecExecution.Value}
    (a : SpecTecExecution.Eval SpecTec.Body plan start left leftFinal)
    (b : SpecTecExecution.Eval SpecTec.Body plan start right rightFinal)
    (plain : Plain plan := by wasm_plain) : left = right ∧ leftFinal = rightFinal :=
  SpecTecExecution.eval_deterministic (eval_plain a plain).1 b

theorem unmatch_excludes_success {plan : SpecTecExecution.Action.{1} SpecTec.Request}
    {start failedFinal successFinal : Nat}
    (failed : SpecTecExecution.Eval SpecTec.Body plan start .unmatch failedFinal)
    (value : SpecTecExecution.Value)
    (success : SpecTecExecution.Eval SpecTec.Body plan start (.success value) successFinal)
    (plain : Plain plan := by wasm_plain) : False :=
  SpecTecExecution.unmatch_excludes_success (eval_plain failed plain).1 value success

end properties.wasm_module_ok.Execution
