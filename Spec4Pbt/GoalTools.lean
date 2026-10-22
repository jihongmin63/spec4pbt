import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.ElabRules
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Meta Elab Term Command

namespace Spec4Pbt

private def permittedAxiom (name : Name) : Bool :=
  name == ``propext || name == ``Quot.sound

private def rejectAxioms (name : Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  let forbidden := axioms.toList.filter (fun candidate => !permittedAxiom candidate)
  unless forbidden.isEmpty do
    throwError "declaration '{name}' depends on forbidden axioms: {forbidden}"

private def rejectModuleAxioms (moduleName : Name) : MetaM Unit := do
  let environment ← getEnv
  unless environment.header.moduleNames.contains moduleName do
    throwError "requested source module '{moduleName}' was not imported"
  for (name, info) in environment.constants.toList do
    if let .axiomInfo _ := info then
      if let some index := environment.getModuleIdxFor? name then
        if environment.header.moduleNames[index]! == moduleName then
          throwError "source module '{moduleName}' declares forbidden axiom '{name}'"

elab "#spec4pbt_verify " proof:ident " in_module " moduleName:ident " : " expectedSyntax:term : command => do
  let proofName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo proof
  let usedAxioms ← liftTermElabM do
    let expected ← elabType expectedSyntax
    synthesizeSyntheticMVarsNoPostponing
    let expected ← instantiateMVars expected
    if expected.hasMVar then
      throwError "expected declaration type contains unresolved metavariables; provide a complete Lean type"
    let info ← getConstInfo proofName
    if info.isUnsafe || info.isPartial then
      throwError "proof '{proofName}' must be a safe, total Lean declaration"
    let proofExpression ← mkConstWithFreshMVarLevels proofName
    let actual ← inferType proofExpression
    unless ← isDefEq actual expected do
      throwError "proof type mismatch for '{proofName}': actual {actual}; expected exactly {expected}. Additional proof hypotheses are not allowed"
    let environment ← getEnv
    let some ownerIndex := environment.getModuleIdxFor? proofName
      | throwError "proof '{proofName}' must be declared in the imported source module '{moduleName.getId}'"
    let owner := environment.header.moduleNames[ownerIndex]!
    unless owner == moduleName.getId do
      throwError "proof '{proofName}' is declared in '{owner}', not requested module '{moduleName.getId}'; verify its defining module directly"
    rejectModuleAxioms moduleName.getId
    rejectAxioms proofName
    for name in expected.getUsedConstants do
      rejectAxioms name
    return (← collectAxioms proofName).toList
  liftIO <| IO.println s!"Verified '{proofName}': exact expected type, no additional hypotheses, no forbidden transitive axioms; axioms used: {usedAxioms}."

end Spec4Pbt
