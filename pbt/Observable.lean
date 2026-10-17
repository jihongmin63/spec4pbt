import pbt.GoalTools
import Lean.Compiler.NoncomputableAttr
import Lean.Compiler.ImplementedByAttr
import Lean.Compiler.ExternAttr
import Lean.Compiler.CSimpAttr

open Lean Meta Elab Term Command

namespace Spec4Pbt.Observable

/-- Compiler rewriting is outside the checker's kernel dependency graph.
Reject custom exported rewrites; conservatively catch erased local rewrites by
rejecting project axioms, sorry-containing declarations, and unsafe proofs.
Trusted core codec foundations remain outside this project policy. -/
private def auditCompilerPolicy : MetaM Unit := do
  let environment ← getEnv
  let runtimePath ← IO.FS.realPath (← getLibDir (← getBuildDir))
  let mut trustedModules : NameMap Bool := {}
  for (name, info) in environment.constants.toList do
    let axiomDeclaration := match info with | .axiomInfo _ => true | _ => false
    let sorryDeclaration := info.getUsedConstantsAsSet.contains ``sorryAx
    let rewriteDeclaration := Compiler.hasCSimpAttribute environment name
    let unsafeProof ← if info.isUnsafe || info.isPartial then isProp info.type else pure false
    unless axiomDeclaration || sorryDeclaration || rewriteDeclaration || unsafeProof do continue
    let some index := environment.getModuleIdxFor? name
      | throwError "compiler policy: declaration '{name}' has no imported module provenance"
    let owner := environment.header.moduleNames[index]!
    let trusted ← match trustedModules.find? owner with
      | some value => pure value
      | none => do
        let path ← IO.FS.realPath (← findOLean owner)
        let value := path.toString.startsWith (runtimePath.toString ++ "/")
        trustedModules := trustedModules.insert owner value
        pure value
    unless trusted do
      if axiomDeclaration then
        throwError "compiler policy: project declaration '{name}' is a forbidden axiom"
      if sorryDeclaration then
        throwError "compiler policy: project declaration '{name}' references sorryAx"
      if rewriteDeclaration then
        throwError "compiler policy: custom csimp rewrite '{name}' is unsupported"
      throwError "compiler policy: project declaration '{name}' is an unsafe proof"

/-- Inspect the implementation dependency graph as well as the proof graph.
The exact type, owner module, and axiom checks live in GoalTools. -/
private partial def audit (pending : List Name) (seen : NameSet) : MetaM Unit := do
  match pending with
  | [] => pure ()
  | name :: rest =>
    if seen.contains name then
      audit rest seen
    else
      let info ← getConstInfo name
      if info.isUnsafe || info.isPartial then
        throwError "declaration '{name}' must be safe and total"
      let environment ← getEnv
      -- Recursive `partial def` is exported as a safe opaque constant. Its
      -- actual implementation is a separate `_unsafe_rec` declaration, unlike
      -- total recursive definitions whose kernel body is a definition.
      if let .opaqueInfo _ := info then
        if (environment.find? (Compiler.mkUnsafeRecName name)).isSome then
          throwError "declaration '{name}' is partial; safe total source code is required"
      if (Compiler.getImplementedBy? environment name).isSome || isExtern environment name then
        let some index := environment.getModuleIdxFor? name
          | throwError "cannot establish runtime provenance for '{name}'"
        let owner := environment.header.moduleNames[index]!
        let objectPath ← IO.FS.realPath (← findOLean owner)
        let runtimePath ← IO.FS.realPath (← getLibDir (← getBuildDir))
        unless objectPath.toString.startsWith (runtimePath.toString ++ "/") do
          throwError "declaration '{name}' uses a runtime implementation override; safe total source code is required"
      audit (info.getUsedConstantsAsSet.toList ++ rest) (seen.insert name)

elab "#spec4pbt_observable_audit " declaration:ident : command => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo declaration
    audit [name] {}

elab "#spec4pbt_observable_executable " declaration:ident : command => do
  liftTermElabM do
    auditCompilerPolicy
    let name ← realizeGlobalConstNoOverloadWithInfo declaration
    if isNoncomputable (← getEnv) name then
      throwError "checker '{name}' is noncomputable; an executable definition is required"
    audit [name] {}

/-- Generated transport freezes codec selection before property imports.
Parser internals may be partial; the wrapper must retain its source implementation. -/
private def auditTransport (name : Name) : MetaM Unit := do
  let environment ← getEnv
  let info ← getConstInfo name
  if info.isUnsafe || info.isPartial || isNoncomputable environment name then
    throwError "transport helper '{name}' must be safe and executable"
  if (Compiler.getImplementedBy? environment name).isSome || isExtern environment name then
    throwError "transport helper '{name}' uses a runtime implementation override"

elab "#spec4pbt_observable_transport " declaration:ident : command => do
  liftTermElabM do
    auditTransport (← realizeGlobalConstNoOverloadWithInfo declaration)

elab "#spec4pbt_observable_transport_type " declaration:ident " in_module " moduleName:ident " : " expectedSyntax:term : command => do
  liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo declaration
    let expected ← elabType expectedSyntax
    synthesizeSyntheticMVarsNoPostponing
    let expected ← instantiateMVars expected
    if expected.hasMVar then throwError "transport type contains unresolved metavariables"
    let actual ← inferType (← mkConstWithFreshMVarLevels name)
    unless ← isDefEq actual expected do
      throwError "transport helper type mismatch for '{name}': actual {actual}; expected {expected}"
    let environment ← getEnv
    let some index := environment.getModuleIdxFor? name
      | throwError "transport helper '{name}' must belong to imported view module"
    unless environment.header.moduleNames[index]! == moduleName.getId do
      throwError "transport helper '{name}' is not declared in view module '{moduleName.getId}'"
    auditTransport name

end Spec4Pbt.Observable
