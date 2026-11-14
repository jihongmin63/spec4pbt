import WasmSpecification
import Lean

set_option autoImplicit false

open Lean Meta Elab Tactic

namespace RustWasm.GroundEvaluation

private structure Evaluation where
  outcome : Expr
  finalSupply : Expr
  proof : Expr
  deriving Inhabited

private def finish (program action supply outcome finalSupply : Expr)
    (constructor : Name) (arguments : Array Expr) : MetaM Evaluation := do
  let expected ← mkAppM ``SpecTecExecution.Eval #[program, action, supply, outcome, finalSupply]
  let proof ← mkFreshExprMVar expected
  let obligations ← proof.mvarId!.apply (← mkConstWithFreshMVarLevels constructor)
  let premises ← obligations.filterM fun obligation => do isProp (← obligation.getType)
  unless premises.length == arguments.size do
    throwError "Execution constructor {constructor} produced {premises.length} premises for {arguments.size} proofs"
  for obligation in premises, argument in arguments do
    unless ← isDefEq (← obligation.getType) (← inferType argument) do
      throwError "Execution constructor {constructor} has an unmatched premise: {← obligation.getType}"
    obligation.assign argument
  for obligation in obligations do
    unless ← obligation.isAssigned do
      throwError "Execution constructor {constructor} has an unresolved witness: {← obligation.getType}"
  return ⟨outcome, finalSupply, ← instantiateMVars proof⟩

private def success (value : Expr) : MetaM Expr := do
  mkAppM ``SpecTecExecution.Outcome.success #[← mkAppM ``SpecTecExecution.Value.of #[value]]

/-- Construct the original Eval derivation directly; the kernel checks every constructor. -/
private partial def evaluate (program action supply : Expr) : MetaM Evaluation := do
  let reduced ← whnf action
  let actionName : Option Name := reduced.getAppFn.constName?
  let arguments := reduced.getAppArgs
  match actionName with
  | some ``SpecTecExecution.Action.pure =>
    let value := arguments[arguments.size - 1]!
    finish program action supply (← success value) supply ``SpecTecExecution.Eval.pure #[]
  | some ``SpecTecExecution.Action.unmatch =>
    let outcome ← mkAppOptM ``SpecTecExecution.Outcome.unmatch #[some (mkConst ``SpecTecExecution.Value)]
    finish program action supply outcome supply ``SpecTecExecution.Eval.unmatch #[]
  | some ``SpecTecExecution.Action.abort =>
    let message := arguments[arguments.size - 1]!
    let outcome ← mkAppOptM ``SpecTecExecution.Outcome.abort #[some (mkConst ``SpecTecExecution.Value), some message]
    finish program action supply outcome supply ``SpecTecExecution.Eval.abort #[]
  | some ``SpecTecExecution.Action.freshId =>
    let value ← mkAppM ``SpecTecExecution.freshName #[supply]
    let finalSupply ← mkAppM ``Nat.succ #[supply]
    finish program action supply (← success value) finalSupply ``SpecTecExecution.Eval.freshId #[]
  | some ``SpecTecExecution.Action.call =>
    let request := arguments[arguments.size - 1]!
    let result ← evaluate program (mkApp program request) supply
    finish program action supply result.outcome result.finalSupply ``SpecTecExecution.Eval.call #[result.proof]
  | some ``SpecTecExecution.Action.guard =>
    let condition := arguments[arguments.size - 1]!
    let decision ← whnf (← mkDecide condition)
    if decision.isConstOf ``Bool.true then
      finish program action supply (← success (mkConst ``Unit.unit)) supply
        ``SpecTecExecution.Eval.guard_true #[← mkDecideProof condition]
    else if decision.isConstOf ``Bool.false then
      let outcome ← mkAppOptM ``SpecTecExecution.Outcome.unmatch #[some (mkConst ``SpecTecExecution.Value)]
      finish program action supply outcome supply ``SpecTecExecution.Eval.guard_false
        #[← mkDecideProof (mkNot condition)]
    else
      throwError "Cannot decide original execution guard: {condition}"
  | some ``SpecTecExecution.Action.bind =>
    let plan := arguments[arguments.size - 2]!
    let next := arguments[arguments.size - 1]!
    let first ← evaluate program plan supply
    match first.outcome.getAppFn.constName? with
    | some ``SpecTecExecution.Outcome.success =>
      let wrapped := first.outcome.getAppArgs.back!
      let value := wrapped.getAppArgs.back!
      let second ← evaluate program (mkApp next value) first.finalSupply
      finish program action supply second.outcome second.finalSupply
        ``SpecTecExecution.Eval.bind_success #[first.proof, second.proof]
    | some ``SpecTecExecution.Outcome.unmatch =>
      finish program action supply first.outcome first.finalSupply
        ``SpecTecExecution.Eval.bind_unmatch #[first.proof]
    | some ``SpecTecExecution.Outcome.abort =>
      finish program action supply first.outcome first.finalSupply
        ``SpecTecExecution.Eval.bind_abort #[first.proof]
    | _ => throwError "Unexpected original execution outcome: {first.outcome}"
  | some ``SpecTecExecution.Action.orElse =>
    let plan := arguments[arguments.size - 2]!
    let next := arguments[arguments.size - 1]!
    let first ← evaluate program plan supply
    match first.outcome.getAppFn.constName? with
    | some ``SpecTecExecution.Outcome.success =>
      finish program action supply first.outcome first.finalSupply
        ``SpecTecExecution.Eval.orElse_success #[first.proof]
    | some ``SpecTecExecution.Outcome.unmatch =>
      let second ← evaluate program (mkApp next (mkConst ``Unit.unit)) first.finalSupply
      finish program action supply second.outcome second.finalSupply
        ``SpecTecExecution.Eval.orElse_unmatch #[first.proof, second.proof]
    | some ``SpecTecExecution.Outcome.abort =>
      finish program action supply first.outcome first.finalSupply
        ``SpecTecExecution.Eval.orElse_abort #[first.proof]
    | _ => throwError "Unexpected original execution outcome: {first.outcome}"
  | some ``SpecTecExecution.Action.notHold =>
    let plan := arguments[arguments.size - 1]!
    let result ← evaluate program plan supply
    match result.outcome.getAppFn.constName? with
    | some ``SpecTecExecution.Outcome.success =>
      let outcome ← mkAppOptM ``SpecTecExecution.Outcome.unmatch #[some (mkConst ``SpecTecExecution.Value)]
      finish program action supply outcome result.finalSupply
        ``SpecTecExecution.Eval.notHold_unmatch #[result.proof]
    | some ``SpecTecExecution.Outcome.unmatch =>
      finish program action supply (← success (mkConst ``Unit.unit)) result.finalSupply
        ``SpecTecExecution.Eval.notHold_success #[result.proof]
    | some ``SpecTecExecution.Outcome.abort =>
      finish program action supply result.outcome result.finalSupply
        ``SpecTecExecution.Eval.notHold_abort #[result.proof]
    | _ => throwError "Unexpected original execution outcome: {result.outcome}"
  | some ``SpecTecExecution.Action.choose =>
    throwError "A ground execution proof requires an explicit witness for choose: {reduced}"
  | _ => throwError "Expected an original execution action, received: {reduced}"

elab "ground_spec_run" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← whnf (← goal.getType)
  unless target.isAppOfArity ``SpecTecExecution.Eval 6 do
    throwError "Expected an original Eval goal, received: {target}"
  let arguments := target.getAppArgs
  let result ← evaluate arguments[1]! arguments[2]! arguments[3]!
  unless ← isDefEq (← inferType result.proof) target do
    throwError "Original execution reached {result.outcome} at supply {result.finalSupply}, but the goal is {target}"
  goal.assign result.proof
  replaceMainGoal []

end RustWasm.GroundEvaluation
