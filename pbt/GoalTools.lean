import Lean.Elab.Command
import Lean.Elab.Term
import Lean.Elab.ElabRules
import Lean.PrettyPrinter
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.Util.CollectLevelParams

open Lean Meta Elab Term Command

namespace Spec4Pbt

private def unfoldPrivateDefinitions (expression : Expr) : MetaM Expr :=
  Meta.transform expression (pre := fun expression => do
    let .const name _ := expression.getAppFn | return .continue
    unless isPrivateName name do return .continue
    let some unfolded ← unfoldDefinition? expression
      | throwError "cannot render private declaration '{name}'"
    return .visit unfolded)

private def expressionSource (expression : Expr) : MetaM String := do
  let expression ← unfoldPrivateDefinitions expression
  withOptions (fun options => options.setBool `pp.fullNames true
      |>.setBool `pp.notation false |>.setBool `pp.explicit true
      |>.setBool `pp.universes true |>.setBool `pp.proofs true
      |>.setBool `pp.tagAppFns true |>.setBool `pp.privateNames true
      |>.set `pp.maxSteps (1000000 : Nat) |>.set `pp.width (120 : Nat)) do
    let rendered ← PrettyPrinter.ppUsing expression fun expression => do
      let (stx, infos) ← PrettyPrinter.delabCore expression (delab := PrettyPrinter.Delaborator.delab)
      -- Root only global constants, using expression tags rather than text.
      -- A spec may itself define Input/Target or use those names for binders.
      let stx ← stx.raw.replaceM fun stx => do
        let some position := PrettyPrinter.Formatter.getExprPos? stx | return none
        let some info := infos[(show SubExpr.Pos from position.byteIdx)]? | return none
        let expression ← match info with
          | .ofTermInfo info => pure info.expr
          | .ofDelabTermInfo info => pure info.expr
          | _ => return none
        let .const name levels := expression.consumeMData | return none
        let identifier := mkIdent (`_root_ ++ name)
        if levels.isEmpty then
          return some identifier.raw
        let levels ← levels.toArray.mapM fun level => PrettyPrinter.delabLevel level 0
        return some (← `($identifier.{$levels,*})).raw
      return ⟨stx⟩
    return rendered.pretty

/-- Definitions denote their universally closed proposition; theorem proofs are
not used. This also supports parameters inherited from Lean sections. -/
private def propertyExpression (name : Name) : MetaM Expr := do
  let info ← getConstInfo name
  match info with
  | .defnInfo _ | .opaqueInfo _ | .inductInfo _ =>
    forallTelescopeReducing info.type fun parameters resultType => do
      unless ← isDefEq resultType (mkSort .zero) do
        throwError "unsupported property '{name}': the declaration must return Prop"
      mkForallFVars parameters (mkAppN (mkConst name (info.levelParams.map Level.param)) parameters)
  | .thmInfo theoremInfo => return theoremInfo.type
  | _ => throwError "unsupported property '{name}': use a Prop-valued definition, opaque, inductive, or theorem"

/-- Retain the public input/premise interface of the original simple example. -/
private def simpleGoal? (claim : Expr) : MetaM (Option (Expr × Expr × Expr × Expr)) := do
  let .forallE _ inputType afterInput .default ← whnf claim | return none
  if (← whnf inputType).isSort then return none
  unless ← isDefEq (← inferType inputType) (mkSort (.succ .zero)) do return none
  withLocalDecl `input .default inputType fun input => do
    let .forallE _ premise afterPremise .default := afterInput.instantiate1 input | return none
    unless ← isProp premise do return none
    if afterPremise.hasLooseBVar 0 then return none
    let conclusion := afterPremise.instantiate1 (mkConst ``True.intro)
    if conclusion.isForall then return none
    let premiseFunction ← mkLambdaFVars #[input] premise
    let targetFunction ← mkLambdaFVars #[input] conclusion
    return some (inputType, premiseFunction, targetFunction, ← mkAppOptM ``Iff.rfl #[some claim])

/-- Pack an arbitrary dependent telescope, including proof and type binders.
The Unit tail ensures the resulting input lives in Type, even for no binders. -/
private def packTelescope (parameters : Array Expr) : MetaM (Expr × Expr) := do
  let mut packedType : Expr := Lean.mkConst ``Unit
  let mut packedValue : Expr := Lean.mkConst ``Unit.unit
  for parameter in parameters.reverse do
    let parameterType ← inferType parameter
    let family := mkLambda `value .default parameterType (packedType.abstract #[parameter])
    packedType ← mkAppM ``PSigma #[family]
    packedValue ← mkAppOptM ``PSigma.mk #[some parameterType, some family, some parameter, some packedValue]
  return (packedType, packedValue)

/-- Universal closure over packed inputs is constructively equivalent to the
source claim. Logical structure inside the remaining target is not rewritten. -/
private def generalGoal (claim : Expr) : MetaM (Expr × Expr × Expr × Expr) :=
  forallTelescopeReducing claim fun parameters conclusion => do
    let (inputType, packedValue) ← packTelescope parameters
    withLocalDecl `input .default inputType fun input => do
      let mut current := input
      let mut arguments := #[]
      for _ in parameters do
        arguments := arguments.push (mkProj ``PSigma 0 current)
        current := mkProj ``PSigma 1 current
      let target := conclusion.replaceFVars parameters arguments
      let premiseFunction ← mkLambdaFVars #[input] (mkConst ``True)
      let targetFunction ← mkLambdaFVars #[input] target
      let testClaim ← mkForallFVars #[input] (← mkArrow (mkConst ``True) target)
      let forward ← withLocalDeclD `property claim fun property =>
        withLocalDeclD `valid (mkConst ``True) fun valid =>
          mkLambdaFVars #[property, input, valid] (mkAppN property arguments)
      let backward ← withLocalDeclD `tested testClaim fun tested => do
        let body := mkApp2 tested packedValue (mkConst ``True.intro)
        mkLambdaFVars #[tested] (← mkLambdaFVars parameters body)
      let equivalence ← mkAppM ``Iff.intro #[forward, backward]
      return (inputType, premiseFunction, targetFunction, equivalence)

/-- Keep the original public claim intact when its internal constants cannot be
printed as Lean source in the generated module. -/
private def closedGoal (claim : Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  let inputType : Expr := mkConst ``Unit
  withLocalDecl `input .default inputType fun input => do
    let premiseFunction ← mkLambdaFVars #[input] (mkConst ``True)
    let targetFunction ← mkLambdaFVars #[input] claim
    let testClaim ← mkForallFVars #[input] (← mkArrow (mkConst ``True) claim)
    let forward ← withLocalDeclD `property claim fun property =>
      withLocalDeclD `valid (mkConst ``True) fun valid =>
        mkLambdaFVars #[property, input, valid] property
    let backward ← withLocalDeclD `tested testClaim fun tested =>
      mkLambdaFVars #[tested] (mkApp2 tested (mkConst ``Unit.unit) (mkConst ``True.intro))
    let equivalence ← mkAppM ``Iff.intro #[forward, backward]
    return (inputType, premiseFunction, targetFunction, equivalence)

private def expressionLevels (expression : Expr) : MetaM (Array String) := do
  let tokens := Parser.getTokenTable (← getEnv)
  return (collectLevelParams {} expression).params.map fun name =>
    name.toStringWithToken (isToken := fun token => (tokens.find? token).isSome)

private def reflectExpressions (claim : Expr) (input : Expr) (premise : Expr)
    (target : Expr) (equivalence : Expr) : MetaM Json := do
  return Json.mkObj [
    ("input", toJson (← expressionSource input)),
    ("premise", toJson (← expressionSource premise)),
    ("target", toJson (← expressionSource target)),
    ("claim", toJson (← expressionSource claim)),
    ("equivalence", toJson (← expressionSource equivalence)),
    ("levels", Json.mkObj [
      ("input", toJson (← expressionLevels input)),
      ("premise", toJson (← expressionLevels premise)),
      ("target", toJson (← expressionLevels target)),
      ("claim", toJson (← expressionLevels claim))])]

/-- Refer to a public declaration when its type contains private constants that
cannot be printed in a generated module. Binder types are inferred from the
declaration's application. -/
private def declarationFallback (name : Name) (claim : Expr) : MetaM Json := do
  let info ← getConstInfo name
  let tokens := Parser.getTokenTable (← getEnv)
  let sourceName (name : Name) :=
    name.toStringWithToken (isToken := fun token => (tokens.find? token).isSome)
  let levelArgs := info.levelParams.map sourceName
  let levelSuffix := if levelArgs.isEmpty then "" else ".{" ++ String.intercalate ", " levelArgs ++ "}"
  let declarationTerm := "@" ++ sourceName (`_root_ ++ name) ++ levelSuffix
  let claimSource ← if info.isTheorem then
      pure ("(type_of% (" ++ declarationTerm ++ "))")
    else
      forallTelescopeReducing info.type fun parameters _ => do
        let names := (List.range parameters.size).map fun index => s!"input{index}"
        let application := "(" ++ declarationTerm ++
          (if names.isEmpty then "" else " " ++ String.intercalate " " names) ++ ")"
        return if names.isEmpty then application
          else "(∀ " ++ String.intercalate " " names ++ ", " ++ application ++ ")"
  let levels ← expressionLevels claim
  return Json.mkObj [
    ("input", toJson ("_root_.Unit" : String)),
    ("premise", toJson ("fun (_ : _root_.Unit) => _root_.True" : String)),
    ("target", toJson ("fun (_ : _root_.Unit) => " ++ claimSource)),
    ("claim", toJson claimSource),
    ("equivalence", toJson ("_root_.Iff.intro (fun property _ _ => property) " ++
      "(fun tested => tested _root_.Unit.unit _root_.True.intro)")),
    ("levels", Json.mkObj [
      ("input", toJson (#[] : Array String)),
      ("premise", toJson (#[] : Array String)),
      ("target", toJson levels),
      ("claim", toJson levels)])]

private def reflectGoal (name : Name) : MetaM Json := do
  let claim ← propertyExpression name
  try
    let (input, premise, target, equivalence) ← match ← simpleGoal? claim with
      | some result => pure result
      | none => generalGoal claim
    reflectExpressions claim input premise target equivalence
  catch original =>
    try
      let (input, premise, target, equivalence) ← closedGoal claim
      reflectExpressions claim input premise target equivalence
    catch _ =>
      try declarationFallback name claim
      catch _ => throw original

elab "#spec4pbt_goal " declaration:ident : command => do
  let result ← liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo declaration
    reflectGoal name
  liftIO <| IO.println ("SPEC4PBT_GOAL " ++ result.compress)

private def rejectAxioms (name : Name) : MetaM Unit := do
  let axioms ← collectAxioms name
  unless axioms.isEmpty do
    throwError "declaration '{name}' depends on forbidden axioms: {axioms.toList}"

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
  liftTermElabM do
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
  liftIO <| IO.println s!"Verified '{proofName}': exact expected type, no additional hypotheses, and zero transitive axioms."

end Spec4Pbt
