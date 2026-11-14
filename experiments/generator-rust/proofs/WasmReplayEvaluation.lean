import WasmChoices
import WasmSequence

set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.ast

private theorem controlCast (source target : UScalarTy) (value : Nat)
    (sourceBound : value < 2^source.numBits) (targetBound : value < 2^target.numBits) :
    UScalar.cast target (@UScalar.ofNatCore source value sourceBound) =
      @UScalar.ofNatCore target value targetBound := by
  apply UScalar.val_eq_imp
  simp only [UScalar.cast_val_eq, UScalar.ofNatCore_val_eq]
  exact Nat.mod_eq_of_lt targetBound


private theorem controlAdd (type : UScalarTy) (left right : UScalar type) :
    left + right = UScalar.add left right := rfl
private theorem controlMul (type : UScalarTy) (left right : UScalar type) :
    left * right = UScalar.mul left right := rfl
private theorem controlSub (type : UScalarTy) (left right : UScalar type)
    (valid : right.val ≤ left.val) :
    left - right = Result.ok (@UScalar.ofNatCore type (left.val - right.val)
      (Nat.lt_of_le_of_lt (Nat.sub_le _ _) left.hBounds)) := by
  apply wp_eq_ok
  apply Aeneas.Std.WP.spec_mono
  · exact UScalar.sub_spec valid
  · intro value property
    apply UScalar.val_eq_imp
    simpa only [UScalar.ofNatCore_val_eq] using property.1
private theorem controlDiv (type : UScalarTy) (left right : UScalar type) :
    left / right = UScalar.div left right := rfl
private theorem controlRem (type : UScalarTy) (left right : UScalar type) :
    left % right = UScalar.rem left right := rfl

private theorem controlRawBindCongr {α β : Type} (x y : Result α) (f : α → Result β)
    (equal : x = y) : Aeneas.Std.bind x f = Aeneas.Std.bind y f := by
  rw [equal]

open Lean Meta in
simproc_decl controlTypeclassBind (@Bind.bind Aeneas.Std.Result _ _ _ _ _) := fun expression => do
  let_expr Bind.bind _ _ _ _ computation continuation := expression | return .continue
  let reduced ← mkAppM ``Aeneas.Std.bind #[computation, continuation]
  let proof ← mkAppM ``Aeneas.Std.bind_tc_eq #[computation, continuation]
  return .visit { expr := reduced, proof? := proof }

-- Reduce each successful operation before visiting its continuation. Result.ok
-- remains folded; every reduction is justified by bind lemmas or definitional equality.
open Lean Meta in
simproc_decl controlRawBind (@Aeneas.Std.bind _ _ _ _) := fun expression => do
  let_expr Aeneas.Std.bind _ _ computation continuation := expression | return .continue
  let result ← Lean.Meta.Simp.simp computation
  let congruence ← mkAppM ``controlRawBindCongr
    #[computation, result.expr, continuation, ← result.getProof]
  let some returned ← withTransparency .all <| whnfUntil result.expr ``Aeneas.Std.Result.ok
    | throwError "Execution bind did not reduce: {result.expr}"
  let_expr Aeneas.Std.Result.ok _ value := returned
    | throwError "Execution bind did not expose a return value: {returned}"
  let identity ← mkAppM ``Aeneas.Std.bind_ok #[value, continuation]
  let valueType ← inferType value
  let payload ← if valueType.isConstOf ``wasm.ast.ValueType || valueType.isConstOf ``wasm.body.Rule then
    withTransparency .all <| whnf value
  else pure value
  let reduced := (mkApp continuation payload).headBeta
  let proof ← mkEqTrans congruence identity
  return .visit { expr := reduced, proof? := proof }

open Lean Meta in
private def controlCondition (condition : Expr) : Simp.SimpM Simp.Result := do
  let result ← Simp.simp condition
  if result.expr.isTrue || result.expr.isFalse then return result
  if let some proof ← (← Simp.getMethods).discharge? result.expr then
    if proof.hasSorry then throwError "Execution condition produced an unfinished proof: {result.expr}"
    let equality ← mkAppM ``eq_true #[proof]
    return { expr := mkConst ``True, proof? := ← mkEqTrans (← result.getProof) equality }
  if let some proof ← (← Simp.getMethods).discharge? (mkNot result.expr) then
    if proof.hasSorry then throwError "Negated execution condition produced an unfinished proof: {result.expr}"
    let equality ← mkAppM ``eq_false #[proof]
    return { expr := mkConst ``False, proof? := ← mkEqTrans (← result.getProof) equality }
  throwError "Unresolved execution condition: {result.expr}"

open Lean Meta in
simproc_decl controlIte (ite _ _ _) := fun expression => do
  let_expr function@ite type condition decision yes no := expression | return .continue
  let result ← controlCondition condition
  let proofName : Name := if result.expr.isTrue then ``ite_cond_eq_true else ``ite_cond_eq_false
  let proof := mkApp (mkApp5 (mkConst proofName function.constLevels!) type condition decision yes no)
    (← result.getProof)
  return .visit { expr := if result.expr.isTrue then yes else no, proof? := proof }

open Lean Meta in
simproc_decl controlDIte (dite _ _ _) := fun expression => do
  let_expr function@dite type condition decision yes no := expression | return .continue
  let result ← controlCondition condition
  let proofName : Name := if result.expr.isTrue then ``dite_cond_eq_true else ``dite_cond_eq_false
  let witnessLemma := if result.expr.isTrue then ``of_eq_true else ``of_eq_false
  let witness := mkApp2 (mkConst witnessLemma) condition (← result.getProof)
  let proof := mkApp (mkApp5 (mkConst proofName function.constLevels!) type condition decision yes no)
    (← result.getProof)
  let reduced := (mkApp (if result.expr.isTrue then yes else no) witness).headBeta
  return .visit { expr := reduced, proof? := proof }

private theorem controlShift : 1#u64 <<< 32#i32 = Result.ok 4294967296#u64 := by
  apply wp_eq_ok
  step*

syntax "wasm_replay_run" : tactic
macro_rules
| `(tactic| wasm_replay_run) => `(tactic|
  simp (config := { maxSteps := 1000000, zetaDelta := true }) (disch := first | decide | scalar_tac)
    [controlCast, controlAdd, controlMul, controlSub, controlDiv, controlRem, controlShift,
     ↓controlTypeclassBind, ↓controlRawBind, ↓controlIte, ↓controlDIte, sequenceLiteral,
     naturalLiteral, positiveLiteral, tapeFromCells,
     wasm.sequence.cons,
     wasm.ast.copy_types, wasm.ast.copy_value, wasm.ast.copy_signature,
     wasm.type_matching.same_natural, wasm.type_matching.containing_group,
     wasm.type_matching.recursive_index, wasm.type_matching.closed_index,
     wasm.type_matching.closed_values, wasm.type_matching.closed_signature,
     wasm.type_matching.closed_parent, wasm.type_matching.closed_members,
     wasm.type_matching.completed, wasm.type_matching.compare_definition,
     wasm.type_matching.same_definition, wasm.type_matching.same_value,
     wasm.body.reference_rules, wasm.body.numeric_rules, wasm.body.leaf_reads,
     wasm.body.nullable_drop_rules, wasm.body.reference_drop_rules,
     wasm.sequence.append,
     wasm.ast.join_types,
     wasm.ast.copy_bytes,
     wasm.natural.copy_positive,
     wasm.natural.copy,
     wasm.ast.copy_block_type,
     wasm.body.equal_types,
     wasm.natural.predecessor,
     wasm.natural.decrement,
     wasm.body.matches_after,
     wasm.natural.increment_positive,
     wasm.natural.increment,
     wasm.sequence.length,
     wasm.natural.double_plus_one,
     wasm.natural.double,
     wasm.natural.positive_difference,
     wasm.natural.difference,
     wasm.body.suffix,
     wasm.subtract,
     wasm.sequence.split_at,
     wasm.body.replace_suffix,
     wasm.sequence.get,
     wasm.lookup,
     wasm.body.block_signature,
     wasm.sequence.snoc,
     wasm.body.set_rules,
     wasm.body.matching_locals,
     wasm.body.read_rules,
     wasm.body.call_rules,
     wasm.body.control_rules,
     wasm.body.indexed_block_rules,
     wasm.body.label_rules,
     wasm.sequence.last,
     wasm.body.result_rules,
     wasm.body.inline_block_rules,
     wasm.body.rules,
     wasm.natural.positive_from_u64,
     wasm.natural.from_u64,
     wasm.choices.tick,
     wasm.choices.pick_word,
     wasm.choices.positive,
     wasm.choices.natural,
     wasm.choices.word,
     wasm.body.constant,
     wasm.natural.positive_to_u64,
     wasm.natural.to_u64,
     wasm.choices.pick_natural,
     wasm.body.leaf,
     wasm.body.leaves,
     wasm.body.drops,
     wasm.body.base,
     wasm.body.push,
     wasm.body.copy_labels,
     wasm.body.label_types,
     wasm.body.pop_body,
     wasm.value_types_loop,
     wasm.value_types,
     wasm.sequence.select,
     wasm.choose,
     wasm.body.step,
     wasm.body.execute,
     wasm.body.generate,
     wasm.choices.length_from,
     wasm.data.text,
     wasm.data.generate,
     wasm.memory.memory,
     wasm.memory_import.generate, wasm.memory.generate,
     wasm.sequence.reverse_into,
     wasm.sequence.reverse,
     wasm.next_export_digits,
     wasm.types.reference, wasm.types.value, wasm.types.values_loop, wasm.types.values,
     wasm.types.locals_loop, wasm.types.locals, wasm.types.parent, wasm.types.headers,
     wasm.types.signature, wasm.types.members, wasm.types.groups, wasm.types.generate,
     wasm.declared_refs,
     wasm.indices_loop,
     wasm.function_indices,
     wasm.functions_loop,
     wasm.exports_loop,
     wasm.generate_exports,
     wasm.start_indices,
     wasm.generate_start,
     wasm.build,
     wasm.replay,
     wasm.ast.Nullability.Insts.CoreCmpPartialEqNullability.eq,
     wasm.ast.Finality.Insts.CoreCmpPartialEqFinality.eq,
     wasm.ast.Nullability.read_discriminant, wasm.ast.Finality.read_discriminant,
     read_discriminant, IScalar.eq_equiv,
     core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default,
     ↓loop.eq_def, ↓Aeneas.Std.uncurry_apply_pair,
     lift,
     core.result.Result.Insts.CoreOpsTry.branch,
     core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
     core.convert.FromSame, core.convert.FromSame.from,
     UScalar.add,
     UScalar.mul,
     UScalar.div,
     UScalar.rem,
     UScalar.tryMk,
     UScalar.tryMkOpt,
     UScalar.eq_equiv,
     U32.max,
     U32.numBits,
     core.num.U32.MAX,
     U32.rMax, core.num.U64.MAX, U64.rMax,
     UScalar.check_bounds])

end RustWasm
