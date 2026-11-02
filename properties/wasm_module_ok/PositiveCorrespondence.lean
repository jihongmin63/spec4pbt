/- Property-local positive runtime refinement for the unchanged Wasm specification.
   Original source identity: s41537f07a12c318563e6aabf63ee533b7bcdb33a44bfeb071c4af4b8ddd8bf9a.
   Executable definitions and erasure proofs are separate; no compiler replacements. -/
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.FailIfNoProgress
import properties.wasm_module_ok.PositivePlans
import properties.wasm_module_ok.PositiveErasure
namespace properties.wasm_module_ok.PositiveRuntime
open SpecTec SpecTecExecution
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
theorem «erase:$min_:clause:0» (input0 : _root_.Nat) (input1 : _root_.Nat) :
    erase («$min_:clause:0» input0 input1) = SpecTec.«$min_:clause:0» input0 input1 := by
  unfold «$min_:clause:0» SpecTec.«$min_:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$min_:clause:1» (input0 : _root_.Nat) (input1 : _root_.Nat) :
    erase («$min_:clause:1» input0 input1) = SpecTec.«$min_:clause:1» input0 input1 := by
  unfold «$min_:clause:1» SpecTec.«$min_:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$rev_:clause:0» (X : Type) (input0 : (_root_.List X)) :
    erase («$rev_:clause:0» X input0) = SpecTec.«$rev_:clause:0» X input0 := by
  unfold «$rev_:clause:0» SpecTec.«$rev_:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$rev_:clause:1» (X : Type) (input0 : (_root_.List X)) :
    erase («$rev_:clause:1» X input0) = SpecTec.«$rev_:clause:1» X input0 := by
  unfold «$rev_:clause:1» SpecTec.«$rev_:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$make_:clause:0» (X_T : Type) (input0 : X_T) (input1 : _root_.Nat) :
    erase («$make_:clause:0» X_T input0 input1) = SpecTec.«$make_:clause:0» X_T input0 input1 := by
  unfold «$make_:clause:0» SpecTec.«$make_:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$make_:clause:1» (X_T : Type) (input0 : X_T) (input1 : _root_.Nat) :
    erase («$make_:clause:1» X_T input0 input1) = SpecTec.«$make_:clause:1» X_T input0 input1 := by
  unfold «$make_:clause:1» SpecTec.«$make_:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$empty_set:clause:0» (K : Type)  :
    erase («$empty_set:clause:0» K) = SpecTec.«$empty_set:clause:0» K := by
  unfold «$empty_set:clause:0» SpecTec.«$empty_set:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$in_set:clause:0» (K_T : Type) [_root_.DecidableEq K_T] (input0 : K_T) (input1 : (set K_T)) :
    erase («$in_set:clause:0» K_T input0 input1) = SpecTec.«$in_set:clause:0» K_T input0 input1 := by
  unfold «$in_set:clause:0» SpecTec.«$in_set:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$map_set:clause:0» (X : Type) (Y : Type) [specTecCompare_0 : _root_.SpecTecCompareKey Y] (input0 : (X → (Call Y))) (input1 : (set X)) :
    erase («$map_set:clause:0» X Y input0 input1) = SpecTec.«$map_set:clause:0» X Y (fun v0 => toOriginal (input0 v0)) input1 := by
  unfold «$map_set:clause:0» SpecTec.«$map_set:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$map_set:clause:1» (X : Type) (Y : Type) [specTecCompare_0 : _root_.SpecTecCompareKey Y] (input0 : (X → (Call Y))) (input1 : (set X)) :
    erase («$map_set:clause:1» X Y input0 input1) = SpecTec.«$map_set:clause:1» X Y (fun v0 => toOriginal (input0 v0)) input1 := by
  unfold «$map_set:clause:1» SpecTec.«$map_set:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$range:clause:0» (input0 : _root_.Nat) :
    erase («$range:clause:0» input0) = SpecTec.«$range:clause:0» input0 := by
  unfold «$range:clause:0» SpecTec.«$range:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$range:clause:1» (input0 : _root_.Nat) :
    erase («$range:clause:1» input0) = SpecTec.«$range:clause:1» input0 := by
  unfold «$range:clause:1» SpecTec.«$range:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$rolldt':clause:0» (input0 : _root_.Nat) (input1 : rectype) :
    erase («$rolldt':clause:0» input0 input1) = SpecTec.«$rolldt':clause:0» input0 input1 := by
  unfold «$rolldt':clause:0» SpecTec.«$rolldt':clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$rolldt':clause:1» (input0 : _root_.Nat) (input1 : rectype) :
    erase («$rolldt':clause:1» input0 input1) = SpecTec.«$rolldt':clause:1» input0 input1 := by
  unfold «$rolldt':clause:1» SpecTec.«$rolldt':clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$min_addrtype:clause:0» (input0 : addrtype) (input1 : addrtype) :
    erase («$min_addrtype:clause:0» input0 input1) = SpecTec.«$min_addrtype:clause:0» input0 input1 := by
  unfold «$min_addrtype:clause:0» SpecTec.«$min_addrtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$min_addrtype:clause:1» (input0 : addrtype) (input1 : addrtype) :
    erase («$min_addrtype:clause:1» input0 input1) = SpecTec.«$min_addrtype:clause:1» input0 input1 := by
  unfold «$min_addrtype:clause:1» SpecTec.«$min_addrtype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$num_size:clause:0» (input0 : numtype) :
    erase («$num_size:clause:0» input0) = SpecTec.«$num_size:clause:0» input0 := by
  unfold «$num_size:clause:0» SpecTec.«$num_size:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$num_size:clause:1» (input0 : numtype) :
    erase («$num_size:clause:1» input0) = SpecTec.«$num_size:clause:1» input0 := by
  unfold «$num_size:clause:1» SpecTec.«$num_size:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$vec_size:clause:0» (input0 : vectype) :
    erase («$vec_size:clause:0» input0) = SpecTec.«$vec_size:clause:0» input0 := by
  unfold «$vec_size:clause:0» SpecTec.«$vec_size:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_vecop:clause:0» (A : Type) (input0 : (vecop A)) :
    erase («$type_vecop:clause:0» A input0) = SpecTec.«$type_vecop:clause:0» A input0 := by
  unfold «$type_vecop:clause:0» SpecTec.«$type_vecop:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_empty:clause:0»  :
    erase («$free_empty:clause:0» ) = SpecTec.«$free_empty:clause:0»  := by
  unfold «$free_empty:clause:0» SpecTec.«$free_empty:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$fold_left:clause:0» (X_T : Type) (Y : Type) (input0 : (X_T → Y → (Call X_T))) (input1 : X_T) (input2 : (_root_.List Y)) :
    erase («$fold_left:clause:0» X_T Y input0 input1 input2) = SpecTec.«$fold_left:clause:0» X_T Y (fun v0 v1 => toOriginal (input0 v0 v1)) input1 input2 := by
  unfold «$fold_left:clause:0» SpecTec.«$fold_left:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$fold_left:clause:1» (X_T : Type) (Y : Type) (input0 : (X_T → Y → (Call X_T))) (input1 : X_T) (input2 : (_root_.List Y)) :
    erase («$fold_left:clause:1» X_T Y input0 input1 input2) = SpecTec.«$fold_left:clause:1» X_T Y (fun v0 v1 => toOriginal (input0 v0 v1)) input1 input2 := by
  unfold «$fold_left:clause:1» SpecTec.«$fold_left:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_union:clause:0» (input0 : free) (input1 : free) :
    erase («$free_union:clause:0» input0 input1) = SpecTec.«$free_union:clause:0» input0 input1 := by
  unfold «$free_union:clause:0» SpecTec.«$free_union:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_unions:clause:0» (input0 : (_root_.List free)) :
    erase («$free_unions:clause:0» input0) = SpecTec.«$free_unions:clause:0» input0 := by
  unfold «$free_unions:clause:0» SpecTec.«$free_unions:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_unions:clause:1» (input0 : (_root_.List SpecTec.free)) :
    erase («$free_unions:clause:1» input0) = SpecTec.«$free_unions:clause:1» input0 := by
  unfold «$free_unions:clause:1» SpecTec.«$free_unions:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$add_minus_one:clause:0» (input0 : idx) :
    erase («$add_minus_one:clause:0» input0) = SpecTec.«$add_minus_one:clause:0» input0 := by
  unfold «$add_minus_one:clause:0» SpecTec.«$add_minus_one:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_idx:clause:0» (input0 : idx) :
    erase («$free_idx:clause:0» input0) = SpecTec.«$free_idx:clause:0» input0 := by
  unfold «$free_idx:clause:0» SpecTec.«$free_idx:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_shift:clause:0» (input0 : (set idx)) :
    erase («$free_shift:clause:0» input0) = SpecTec.«$free_shift:clause:0» input0 := by
  unfold «$free_shift:clause:0» SpecTec.«$free_shift:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_list:clause:0» (X : Type) (input0 : (X → (Call free))) (input1 : (_root_.List X)) :
    erase («$free_list:clause:0» X input0 input1) = SpecTec.«$free_list:clause:0» X (fun v0 => toOriginal (input0 v0)) input1 := by
  unfold «$free_list:clause:0» SpecTec.«$free_list:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_list:clause:1» (X : Type) (input0 : (X → (Call free))) (input1 : (_root_.List X)) :
    erase («$free_list:clause:1» X input0 input1) = SpecTec.«$free_list:clause:1» X (fun v0 => toOriginal (input0 v0)) input1 := by
  unfold «$free_list:clause:1» SpecTec.«$free_list:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_opt:clause:0» (X_T : Type) (input0 : (X_T → (Call free))) (input1 : (_root_.Option X_T)) :
    erase («$free_opt:clause:0» X_T input0 input1) = SpecTec.«$free_opt:clause:0» X_T (fun v0 => toOriginal (input0 v0)) input1 := by
  unfold «$free_opt:clause:0» SpecTec.«$free_opt:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_opt:clause:1» (X_T : Type) (input0 : (X_T → (Call free))) (input1 : (_root_.Option X_T)) :
    erase («$free_opt:clause:1» X_T input0 input1) = SpecTec.«$free_opt:clause:1» X_T (fun v0 => toOriginal (input0 v0)) input1 := by
  unfold «$free_opt:clause:1» SpecTec.«$free_opt:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_packtype:clause:0» (input0 : packtype) :
    erase («$free_packtype:clause:0» input0) = SpecTec.«$free_packtype:clause:0» input0 := by
  unfold «$free_packtype:clause:0» SpecTec.«$free_packtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_numtype:clause:0» (input0 : numtype) :
    erase («$free_numtype:clause:0» input0) = SpecTec.«$free_numtype:clause:0» input0 := by
  unfold «$free_numtype:clause:0» SpecTec.«$free_numtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_vectype:clause:0» (input0 : vectype) :
    erase («$free_vectype:clause:0» input0) = SpecTec.«$free_vectype:clause:0» input0 := by
  unfold «$free_vectype:clause:0» SpecTec.«$free_vectype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$update_types:clause:0» (input0 : (set typeidx)) :
    erase («$update_types:clause:0» input0) = SpecTec.«$update_types:clause:0» input0 := by
  unfold «$update_types:clause:0» SpecTec.«$update_types:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$update_globals:clause:0» (input0 : (set globalidx)) :
    erase («$update_globals:clause:0» input0) = SpecTec.«$update_globals:clause:0» input0 := by
  unfold «$update_globals:clause:0» SpecTec.«$update_globals:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$update_tables:clause:0» (input0 : (set tableidx)) :
    erase («$update_tables:clause:0» input0) = SpecTec.«$update_tables:clause:0» input0 := by
  unfold «$update_tables:clause:0» SpecTec.«$update_tables:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$update_mems:clause:0» (input0 : (set memidx)) :
    erase («$update_mems:clause:0» input0) = SpecTec.«$update_mems:clause:0» input0 := by
  unfold «$update_mems:clause:0» SpecTec.«$update_mems:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$update_tags:clause:0» (input0 : (set tagidx)) :
    erase («$update_tags:clause:0» input0) = SpecTec.«$update_tags:clause:0» input0 := by
  unfold «$update_tags:clause:0» SpecTec.«$update_tags:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$update_funcs:clause:0» (input0 : (set funcidx)) :
    erase («$update_funcs:clause:0» input0) = SpecTec.«$update_funcs:clause:0» input0 := by
  unfold «$update_funcs:clause:0» SpecTec.«$update_funcs:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_start:clause:0» (input0 : SpecTec.start) :
    erase («$free_start:clause:0» input0) = SpecTec.«$free_start:clause:0» input0 := by
  unfold «$free_start:clause:0» SpecTec.«$free_start:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$update_elems:clause:0» (input0 : (set elemidx)) :
    erase («$update_elems:clause:0» input0) = SpecTec.«$update_elems:clause:0» input0 := by
  unfold «$update_elems:clause:0» SpecTec.«$update_elems:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$update_datas:clause:0» (input0 : (set dataidx)) :
    erase («$update_datas:clause:0» input0) = SpecTec.«$update_datas:clause:0» input0 := by
  unfold «$update_datas:clause:0» SpecTec.«$update_datas:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$update_locals:clause:0» (input0 : (set localidx)) :
    erase («$update_locals:clause:0» input0) = SpecTec.«$update_locals:clause:0» input0 := by
  unfold «$update_locals:clause:0» SpecTec.«$update_locals:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$update_labels:clause:0» (input0 : (set labelidx)) :
    erase («$update_labels:clause:0» input0) = SpecTec.«$update_labels:clause:0» input0 := by
  unfold «$update_labels:clause:0» SpecTec.«$update_labels:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$update_label:clause:0» (input0 : idx) :
    erase («$update_label:clause:0» input0) = SpecTec.«$update_label:clause:0» input0 := by
  unfold «$update_label:clause:0» SpecTec.«$update_label:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_memtype:clause:0» (input0 : memtype) :
    erase («$free_memtype:clause:0» input0) = SpecTec.«$free_memtype:clause:0» input0 := by
  unfold «$free_memtype:clause:0» SpecTec.«$free_memtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_mem:clause:0» (input0 : memory) :
    erase («$free_mem:clause:0» input0) = SpecTec.«$free_mem:clause:0» input0 := by
  unfold «$free_mem:clause:0» SpecTec.«$free_mem:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_numtype:clause:0» (input0 : (_root_.List deftype)) (input1 : numtype) (input2 : numtype) :
    erase («$match_numtype:clause:0» input0 input1 input2) = SpecTec.«$match_numtype:clause:0» input0 input1 input2 := by
  unfold «$match_numtype:clause:0» SpecTec.«$match_numtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_numtype:clause:1» (input0 : (_root_.List deftype)) (input1 : numtype) (input2 : numtype) :
    erase («$match_numtype:clause:1» input0 input1 input2) = SpecTec.«$match_numtype:clause:1» input0 input1 input2 := by
  unfold «$match_numtype:clause:1» SpecTec.«$match_numtype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_vectype:clause:0» (input0 : (_root_.List deftype)) (input1 : vectype) (input2 : vectype) :
    erase («$match_vectype:clause:0» input0 input1 input2) = SpecTec.«$match_vectype:clause:0» input0 input1 input2 := by
  unfold «$match_vectype:clause:0» SpecTec.«$match_vectype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_packtype:clause:0» (input0 : (_root_.List deftype)) (input1 : packtype) (input2 : packtype) :
    erase («$match_packtype:clause:0» input0 input1 input2) = SpecTec.«$match_packtype:clause:0» input0 input1 input2 := by
  unfold «$match_packtype:clause:0» SpecTec.«$match_packtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$empty_context:clause:0»  :
    erase («$empty_context:clause:0» ) = SpecTec.«$empty_context:clause:0»  := by
  unfold «$empty_context:clause:0» SpecTec.«$empty_context:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$stack:clause:0» (input0 : SpecTec.resulttype) :
    erase («$stack:clause:0» input0) = SpecTec.«$stack:clause:0» input0 := by
  unfold «$stack:clause:0» SpecTec.«$stack:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$peek:clause:0» (input0 : _root_.Nat) (input1 : inferresulttype) :
    erase («$peek:clause:0» input0 input1) = SpecTec.«$peek:clause:0» input0 input1 := by
  unfold «$peek:clause:0» SpecTec.«$peek:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$peek:clause:1» (input0 : _root_.Nat) (input1 : inferresulttype) :
    erase («$peek:clause:1» input0 input1) = SpecTec.«$peek:clause:1» input0 input1 := by
  unfold «$peek:clause:1» SpecTec.«$peek:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$local:clause:0» (input0 : context) (input1 : typeidx) :
    erase («$local:clause:0» input0 input1) = SpecTec.«$local:clause:0» input0 input1 := by
  unfold «$local:clause:0» SpecTec.«$local:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$init_local:clause:0» (input0 : context) (input1 : typeidx) :
    erase («$init_local:clause:0» input0 input1) = SpecTec.«$init_local:clause:0» input0 input1 := by
  unfold «$init_local:clause:0» SpecTec.«$init_local:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$init_locals:clause:0» (input0 : context) (input1 : (_root_.List typeidx)) :
    erase («$init_locals:clause:0» input0 input1) = SpecTec.«$init_locals:clause:0» input0 input1 := by
  unfold «$init_locals:clause:0» SpecTec.«$init_locals:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$init_locals:clause:1» (input0 : context) (input1 : (_root_.List typeidx)) :
    erase («$init_locals:clause:1» input0 input1) = SpecTec.«$init_locals:clause:1» input0 input1 := by
  unfold «$init_locals:clause:1» SpecTec.«$init_locals:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$init_valtypes:clause:0» (input0 : inferresulttype) (input1 : _root_.Nat) (input2 : _root_.Nat) :
    erase («$init_valtypes:clause:0» input0 input1 input2) = SpecTec.«$init_valtypes:clause:0» input0 input1 input2 := by
  unfold «$init_valtypes:clause:0» SpecTec.«$init_valtypes:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$init_valtypes:clause:1» (input0 : inferresulttype) (input1 : _root_.Nat) (input2 : _root_.Nat) :
    erase («$init_valtypes:clause:1» input0 input1 input2) = SpecTec.«$init_valtypes:clause:1» input0 input1 input2 := by
  unfold «$init_valtypes:clause:1» SpecTec.«$init_valtypes:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Numtype_ok:clause:0» (input0 : context) (input1 : SpecTec.numtype) :
    erase («Numtype_ok:clause:0» input0 input1) = SpecTec.«Numtype_ok:clause:0» input0 input1 := by
  unfold «Numtype_ok:clause:0» SpecTec.«Numtype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Vectype_ok:clause:0» (input0 : context) (input1 : SpecTec.vectype) :
    erase («Vectype_ok:clause:0» input0 input1) = SpecTec.«Vectype_ok:clause:0» input0 input1 := by
  unfold «Vectype_ok:clause:0» SpecTec.«Vectype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Limits_ok:clause:0» (input0 : context) (input1 : SpecTec.range) (input2 : limits) :
    erase («Limits_ok:clause:0» input0 input1 input2) = SpecTec.«Limits_ok:clause:0» input0 input1 input2 := by
  unfold «Limits_ok:clause:0» SpecTec.«Limits_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Limits_ok:clause:1» (input0 : context) (input1 : SpecTec.range) (input2 : limits) :
    erase («Limits_ok:clause:1» input0 input1 input2) = SpecTec.«Limits_ok:clause:1» input0 input1 input2 := by
  unfold «Limits_ok:clause:1» SpecTec.«Limits_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:br_table:iter:3:clause:0» (input0 : context) (input1 : (_root_.List idx)) :
    erase («Instr_ok:br_table:iter:3:clause:0» input0 input1) = SpecTec.«Instr_ok:br_table:iter:3:clause:0» input0 input1 := by
  unfold «Instr_ok:br_table:iter:3:clause:0» SpecTec.«Instr_ok:br_table:iter:3:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:br_table:iter:3:clause:1» (input0 : context) (input1 : (_root_.List idx)) :
    erase («Instr_ok:br_table:iter:3:clause:1» input0 input1) = SpecTec.«Instr_ok:br_table:iter:3:clause:1» input0 input1 := by
  unfold «Instr_ok:br_table:iter:3:clause:1» SpecTec.«Instr_ok:br_table:iter:3:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$check_lane_index:clause:0» (input0 : (_root_.List _root_.Nat)) :
    erase («$check_lane_index:clause:0» input0) = SpecTec.«$check_lane_index:clause:0» input0 := by
  unfold «$check_lane_index:clause:0» SpecTec.«$check_lane_index:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$check_lane_index:clause:1» (input0 : (_root_.List _root_.Nat)) :
    erase («$check_lane_index:clause:1» input0) = SpecTec.«$check_lane_index:clause:1» input0 := by
  unfold «$check_lane_index:clause:1» SpecTec.«$check_lane_index:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$check_lane_index:clause:2» (input0 : (_root_.List _root_.Nat)) :
    erase («$check_lane_index:clause:2» input0) = SpecTec.«$check_lane_index:clause:2» input0 := by
  unfold «$check_lane_index:clause:2» SpecTec.«$check_lane_index:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Funcbody_ok:rule:iter:2:clause:0» (input0 : (_root_.List valtype)) :
    erase («Funcbody_ok:rule:iter:2:clause:0» input0) = SpecTec.«Funcbody_ok:rule:iter:2:clause:0» input0 := by
  unfold «Funcbody_ok:rule:iter:2:clause:0» SpecTec.«Funcbody_ok:rule:iter:2:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Funcbody_ok:rule:iter:2:clause:1» (input0 : (_root_.List valtype)) :
    erase («Funcbody_ok:rule:iter:2:clause:1» input0) = SpecTec.«Funcbody_ok:rule:iter:2:clause:1» input0 := by
  unfold «Funcbody_ok:rule:iter:2:clause:1» SpecTec.«Funcbody_ok:rule:iter:2:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$numtype_of_addrtype:clause:0» (input0 : addrtype) :
    erase («$numtype_of_addrtype:clause:0» input0) = SpecTec.«$numtype_of_addrtype:clause:0» input0 := by
  unfold «$numtype_of_addrtype:clause:0» SpecTec.«$numtype_of_addrtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$numtype_of_addrtype:clause:1» (input0 : addrtype) :
    erase («$numtype_of_addrtype:clause:1» input0) = SpecTec.«$numtype_of_addrtype:clause:1» input0 := by
  unfold «$numtype_of_addrtype:clause:1» SpecTec.«$numtype_of_addrtype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Memtype_ok:clause:0» (input0 : context) (input1 : memtype) :
    erase («Memtype_ok:clause:0» input0 input1) = SpecTec.«Memtype_ok:clause:0» input0 input1 := by
  unfold «Memtype_ok:clause:0» SpecTec.«Memtype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Memtype_ok:clause:1» (input0 : context) (input1 : memtype) :
    erase («Memtype_ok:clause:1» input0 input1) = SpecTec.«Memtype_ok:clause:1» input0 input1 := by
  unfold «Memtype_ok:clause:1» SpecTec.«Memtype_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Vstoreop_ok:clause:0» (input0 : context) (input1 : vstoreop_) :
    erase («Vstoreop_ok:clause:0» input0 input1) = SpecTec.«Vstoreop_ok:clause:0» input0 input1 := by
  unfold «Vstoreop_ok:clause:0» SpecTec.«Vstoreop_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Vstoreop_ok:clause:1» (input0 : context) (input1 : vstoreop_) :
    erase («Vstoreop_ok:clause:1» input0 input1) = SpecTec.«Vstoreop_ok:clause:1» input0 input1 := by
  unfold «Vstoreop_ok:clause:1» SpecTec.«Vstoreop_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Mem_ok:clause:0» (input0 : context) (input1 : memory) :
    erase («Mem_ok:clause:0» input0 input1) = SpecTec.«Mem_ok:clause:0» input0 input1 := by
  unfold «Mem_ok:clause:0» SpecTec.«Mem_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Mems_ok:clause:0» (input0 : context) (input1 : (_root_.List memory)) :
    erase («Mems_ok:clause:0» input0 input1) = SpecTec.«Mems_ok:clause:0» input0 input1 := by
  unfold «Mems_ok:clause:0» SpecTec.«Mems_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Mems_ok:clause:1» (input0 : context) (input1 : (_root_.List memory)) :
    erase («Mems_ok:clause:1» input0 input1) = SpecTec.«Mems_ok:clause:1» input0 input1 := by
  unfold «Mems_ok:clause:1» SpecTec.«Mems_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_catch:clause:0» (input0 : SpecTec.«catch») :
    erase («$free_catch:clause:0» input0) = SpecTec.«$free_catch:clause:0» input0 := by
  unfold «$free_catch:clause:0» SpecTec.«$free_catch:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_catch:clause:1» (input0 : SpecTec.«catch») :
    erase («$free_catch:clause:1» input0) = SpecTec.«$free_catch:clause:1» input0 := by
  unfold «$free_catch:clause:1» SpecTec.«$free_catch:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_catch:clause:2» (input0 : SpecTec.«catch») :
    erase («$free_catch:clause:2» input0) = SpecTec.«$free_catch:clause:2» input0 := by
  unfold «$free_catch:clause:2» SpecTec.«$free_catch:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_catch:clause:3» (input0 : SpecTec.«catch») :
    erase («$free_catch:clause:3» input0) = SpecTec.«$free_catch:clause:3» input0 := by
  unfold «$free_catch:clause:3» SpecTec.«$free_catch:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$push:clause:0» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) :
    erase («$push:clause:0» input0 input1 input2) = SpecTec.«$push:clause:0» input0 input1 input2 := by
  unfold «$push:clause:0» SpecTec.«$push:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$push:clause:1» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) :
    erase («$push:clause:1» input0 input1 input2) = SpecTec.«$push:clause:1» input0 input1 input2 := by
  unfold «$push:clause:1» SpecTec.«$push:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$push:clause:2» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) :
    erase («$push:clause:2» input0 input1 input2) = SpecTec.«$push:clause:2» input0 input1 input2 := by
  unfold «$push:clause:2» SpecTec.«$push:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_exportdesc:clause:0» (input0 : SpecTec.exportdesc) :
    erase («$free_exportdesc:clause:0» input0) = SpecTec.«$free_exportdesc:clause:0» input0 := by
  unfold «$free_exportdesc:clause:0» SpecTec.«$free_exportdesc:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_exportdesc:clause:1» (input0 : SpecTec.exportdesc) :
    erase («$free_exportdesc:clause:1» input0) = SpecTec.«$free_exportdesc:clause:1» input0 := by
  unfold «$free_exportdesc:clause:1» SpecTec.«$free_exportdesc:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_exportdesc:clause:2» (input0 : SpecTec.exportdesc) :
    erase («$free_exportdesc:clause:2» input0) = SpecTec.«$free_exportdesc:clause:2» input0 := by
  unfold «$free_exportdesc:clause:2» SpecTec.«$free_exportdesc:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_exportdesc:clause:3» (input0 : SpecTec.exportdesc) :
    erase («$free_exportdesc:clause:3» input0) = SpecTec.«$free_exportdesc:clause:3» input0 := by
  unfold «$free_exportdesc:clause:3» SpecTec.«$free_exportdesc:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_exportdesc:clause:4» (input0 : SpecTec.exportdesc) :
    erase («$free_exportdesc:clause:4» input0) = SpecTec.«$free_exportdesc:clause:4» input0 := by
  unfold «$free_exportdesc:clause:4» SpecTec.«$free_exportdesc:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_export:clause:0» (input0 : SpecTec.«export») :
    erase («$free_export:clause:0» input0) = SpecTec.«$free_export:clause:0» input0 := by
  unfold «$free_export:clause:0» SpecTec.«$free_export:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Export_ok:clause:0» (input0 : context) (input1 : SpecTec.nameset) (input2 : «export») :
    erase («Export_ok:clause:0» input0 input1 input2) = SpecTec.«Export_ok:clause:0» input0 input1 input2 := by
  unfold «Export_ok:clause:0» SpecTec.«Export_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Export_ok:clause:1» (input0 : context) (input1 : SpecTec.nameset) (input2 : «export») :
    erase («Export_ok:clause:1» input0 input1 input2) = SpecTec.«Export_ok:clause:1» input0 input1 input2 := by
  unfold «Export_ok:clause:1» SpecTec.«Export_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Export_ok:clause:2» (input0 : context) (input1 : SpecTec.nameset) (input2 : «export») :
    erase («Export_ok:clause:2» input0 input1 input2) = SpecTec.«Export_ok:clause:2» input0 input1 input2 := by
  unfold «Export_ok:clause:2» SpecTec.«Export_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Export_ok:clause:3» (input0 : context) (input1 : SpecTec.nameset) (input2 : «export») :
    erase («Export_ok:clause:3» input0 input1 input2) = SpecTec.«Export_ok:clause:3» input0 input1 input2 := by
  unfold «Export_ok:clause:3» SpecTec.«Export_ok:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Export_ok:clause:4» (input0 : context) (input1 : SpecTec.nameset) (input2 : «export») :
    erase («Export_ok:clause:4» input0 input1 input2) = SpecTec.«Export_ok:clause:4» input0 input1 input2 := by
  unfold «Export_ok:clause:4» SpecTec.«Export_ok:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Exports_ok:clause:0» (input0 : context) (input1 : nameset) (input2 : (_root_.List «export»)) :
    erase («Exports_ok:clause:0» input0 input1 input2) = SpecTec.«Exports_ok:clause:0» input0 input1 input2 := by
  unfold «Exports_ok:clause:0» SpecTec.«Exports_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Exports_ok:clause:1» (input0 : context) (input1 : nameset) (input2 : (_root_.List «export»)) :
    erase («Exports_ok:clause:1» input0 input1 input2) = SpecTec.«Exports_ok:clause:1» input0 input1 input2 := by
  unfold «Exports_ok:clause:1» SpecTec.«Exports_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_externop:clause:0» (input0 : externop_) :
    erase («$type_externop:clause:0» input0) = SpecTec.«$type_externop:clause:0» input0 := by
  unfold «$type_externop:clause:0» SpecTec.«$type_externop:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_externop:clause:1» (input0 : externop_) :
    erase («$type_externop:clause:1» input0) = SpecTec.«$type_externop:clause:1» input0 := by
  unfold «$type_externop:clause:1» SpecTec.«$type_externop:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:0» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:0» input0 input1) = SpecTec.«$is_const:clause:0» input0 input1 := by
  unfold «$is_const:clause:0» SpecTec.«$is_const:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:1» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:1» input0 input1) = SpecTec.«$is_const:clause:1» input0 input1 := by
  unfold «$is_const:clause:1» SpecTec.«$is_const:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:2» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:2» input0 input1) = SpecTec.«$is_const:clause:2» input0 input1 := by
  unfold «$is_const:clause:2» SpecTec.«$is_const:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:3» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:3» input0 input1) = SpecTec.«$is_const:clause:3» input0 input1 := by
  unfold «$is_const:clause:3» SpecTec.«$is_const:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:4» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:4» input0 input1) = SpecTec.«$is_const:clause:4» input0 input1 := by
  unfold «$is_const:clause:4» SpecTec.«$is_const:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:5» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:5» input0 input1) = SpecTec.«$is_const:clause:5» input0 input1 := by
  unfold «$is_const:clause:5» SpecTec.«$is_const:clause:5»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:6» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:6» input0 input1) = SpecTec.«$is_const:clause:6» input0 input1 := by
  unfold «$is_const:clause:6» SpecTec.«$is_const:clause:6»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:7» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:7» input0 input1) = SpecTec.«$is_const:clause:7» input0 input1 := by
  unfold «$is_const:clause:7» SpecTec.«$is_const:clause:7»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:8» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:8» input0 input1) = SpecTec.«$is_const:clause:8» input0 input1 := by
  unfold «$is_const:clause:8» SpecTec.«$is_const:clause:8»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:9» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:9» input0 input1) = SpecTec.«$is_const:clause:9» input0 input1 := by
  unfold «$is_const:clause:9» SpecTec.«$is_const:clause:9»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:10» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:10» input0 input1) = SpecTec.«$is_const:clause:10» input0 input1 := by
  unfold «$is_const:clause:10» SpecTec.«$is_const:clause:10»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_const:clause:11» (input0 : context) (input1 : SpecTec.instr) :
    erase («$is_const:clause:11» input0 input1) = SpecTec.«$is_const:clause:11» input0 input1 := by
  unfold «$is_const:clause:11» SpecTec.«$is_const:clause:11»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Const_ok:rule:iter:0:clause:0» (input0 : context) (input1 : (_root_.List instr)) :
    erase («Const_ok:rule:iter:0:clause:0» input0 input1) = SpecTec.«Const_ok:rule:iter:0:clause:0» input0 input1 := by
  unfold «Const_ok:rule:iter:0:clause:0» SpecTec.«Const_ok:rule:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Const_ok:rule:iter:0:clause:1» (input0 : context) (input1 : (_root_.List SpecTec.instr)) :
    erase («Const_ok:rule:iter:0:clause:1» input0 input1) = SpecTec.«Const_ok:rule:iter:0:clause:1» input0 input1 := by
  unfold «Const_ok:rule:iter:0:clause:1» SpecTec.«Const_ok:rule:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_lane:clause:0» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) :
    erase («$type_lane:clause:0» A B C D E F input0) = SpecTec.«$type_lane:clause:0» A B C D E F input0 := by
  unfold «$type_lane:clause:0» SpecTec.«$type_lane:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_lane:clause:1» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) :
    erase («$type_lane:clause:1» A B C D E F input0) = SpecTec.«$type_lane:clause:1» A B C D E F input0 := by
  unfold «$type_lane:clause:1» SpecTec.«$type_lane:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_lane:clause:2» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) :
    erase («$type_lane:clause:2» A B C D E F input0) = SpecTec.«$type_lane:clause:2» A B C D E F input0 := by
  unfold «$type_lane:clause:2» SpecTec.«$type_lane:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_lane:clause:3» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) :
    erase («$type_lane:clause:3» A B C D E F input0) = SpecTec.«$type_lane:clause:3» A B C D E F input0 := by
  unfold «$type_lane:clause:3» SpecTec.«$type_lane:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_lane:clause:4» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) :
    erase («$type_lane:clause:4» A B C D E F input0) = SpecTec.«$type_lane:clause:4» A B C D E F input0 := by
  unfold «$type_lane:clause:4» SpecTec.«$type_lane:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_lane:clause:5» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (laneop A B C D E F)) :
    erase («$type_lane:clause:5» A B C D E F input0) = SpecTec.«$type_lane:clause:5» A B C D E F input0 := by
  unfold «$type_lane:clause:5» SpecTec.«$type_lane:clause:5»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_vec_lane:clause:0» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) :
    erase («$type_vec_lane:clause:0» A_T B_T C_T D_T E_T F_T input0) = SpecTec.«$type_vec_lane:clause:0» A_T B_T C_T D_T E_T F_T input0 := by
  unfold «$type_vec_lane:clause:0» SpecTec.«$type_vec_lane:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_vec_lane:clause:1» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) :
    erase («$type_vec_lane:clause:1» A_T B_T C_T D_T E_T F_T input0) = SpecTec.«$type_vec_lane:clause:1» A_T B_T C_T D_T E_T F_T input0 := by
  unfold «$type_vec_lane:clause:1» SpecTec.«$type_vec_lane:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_vec_lane:clause:2» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) :
    erase («$type_vec_lane:clause:2» A_T B_T C_T D_T E_T F_T input0) = SpecTec.«$type_vec_lane:clause:2» A_T B_T C_T D_T E_T F_T input0 := by
  unfold «$type_vec_lane:clause:2» SpecTec.«$type_vec_lane:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_vec_lane:clause:3» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) :
    erase («$type_vec_lane:clause:3» A_T B_T C_T D_T E_T F_T input0) = SpecTec.«$type_vec_lane:clause:3» A_T B_T C_T D_T E_T F_T input0 := by
  unfold «$type_vec_lane:clause:3» SpecTec.«$type_vec_lane:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_vec_lane:clause:4» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) :
    erase («$type_vec_lane:clause:4» A_T B_T C_T D_T E_T F_T input0) = SpecTec.«$type_vec_lane:clause:4» A_T B_T C_T D_T E_T F_T input0 := by
  unfold «$type_vec_lane:clause:4» SpecTec.«$type_vec_lane:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_vec_lane:clause:5» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (E_T : Type) (F_T : Type) (input0 : (vecop (laneop A_T B_T C_T D_T E_T F_T))) :
    erase («$type_vec_lane:clause:5» A_T B_T C_T D_T E_T F_T input0) = SpecTec.«$type_vec_lane:clause:5» A_T B_T C_T D_T E_T F_T input0 := by
  unfold «$type_vec_lane:clause:5» SpecTec.«$type_vec_lane:clause:5»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_extractop:clause:0» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) :
    erase («$lane_extractop:clause:0» input0) = SpecTec.«$lane_extractop:clause:0» input0 := by
  unfold «$lane_extractop:clause:0» SpecTec.«$lane_extractop:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_extractop:clause:1» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) :
    erase («$lane_extractop:clause:1» input0) = SpecTec.«$lane_extractop:clause:1» input0 := by
  unfold «$lane_extractop:clause:1» SpecTec.«$lane_extractop:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_extractop:clause:2» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) :
    erase («$lane_extractop:clause:2» input0) = SpecTec.«$lane_extractop:clause:2» input0 := by
  unfold «$lane_extractop:clause:2» SpecTec.«$lane_extractop:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_extractop:clause:3» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) :
    erase («$lane_extractop:clause:3» input0) = SpecTec.«$lane_extractop:clause:3» input0 := by
  unfold «$lane_extractop:clause:3» SpecTec.«$lane_extractop:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_extractop:clause:4» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) :
    erase («$lane_extractop:clause:4» input0) = SpecTec.«$lane_extractop:clause:4» input0 := by
  unfold «$lane_extractop:clause:4» SpecTec.«$lane_extractop:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_extractop:clause:5» (input0 : (vecop (laneop (vnextractop extension) (vnextractop extension) (vnextractop void) (vnextractop void) (vnextractop void) (vnextractop void)))) :
    erase («$lane_extractop:clause:5» input0) = SpecTec.«$lane_extractop:clause:5» input0 := by
  unfold «$lane_extractop:clause:5» SpecTec.«$lane_extractop:clause:5»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_replaceop:clause:0» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) :
    erase («$lane_replaceop:clause:0» input0) = SpecTec.«$lane_replaceop:clause:0» input0 := by
  unfold «$lane_replaceop:clause:0» SpecTec.«$lane_replaceop:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_replaceop:clause:1» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) :
    erase («$lane_replaceop:clause:1» input0) = SpecTec.«$lane_replaceop:clause:1» input0 := by
  unfold «$lane_replaceop:clause:1» SpecTec.«$lane_replaceop:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_replaceop:clause:2» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) :
    erase («$lane_replaceop:clause:2» input0) = SpecTec.«$lane_replaceop:clause:2» input0 := by
  unfold «$lane_replaceop:clause:2» SpecTec.«$lane_replaceop:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_replaceop:clause:3» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) :
    erase («$lane_replaceop:clause:3» input0) = SpecTec.«$lane_replaceop:clause:3» input0 := by
  unfold «$lane_replaceop:clause:3» SpecTec.«$lane_replaceop:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_replaceop:clause:4» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) :
    erase («$lane_replaceop:clause:4» input0) = SpecTec.«$lane_replaceop:clause:4» input0 := by
  unfold «$lane_replaceop:clause:4» SpecTec.«$lane_replaceop:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$lane_replaceop:clause:5» (input0 : (vecop (laneop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop vnreplaceop))) :
    erase («$lane_replaceop:clause:5» input0) = SpecTec.«$lane_replaceop:clause:5» input0 := by
  unfold «$lane_replaceop:clause:5» SpecTec.«$lane_replaceop:clause:5»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$num_lanes:clause:0» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) :
    erase («$num_lanes:clause:0» A B C D E F input0) = SpecTec.«$num_lanes:clause:0» A B C D E F input0 := by
  unfold «$num_lanes:clause:0» SpecTec.«$num_lanes:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$num_lanes:clause:1» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) :
    erase («$num_lanes:clause:1» A B C D E F input0) = SpecTec.«$num_lanes:clause:1» A B C D E F input0 := by
  unfold «$num_lanes:clause:1» SpecTec.«$num_lanes:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$num_lanes:clause:2» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) :
    erase («$num_lanes:clause:2» A B C D E F input0) = SpecTec.«$num_lanes:clause:2» A B C D E F input0 := by
  unfold «$num_lanes:clause:2» SpecTec.«$num_lanes:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$num_lanes:clause:3» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) :
    erase («$num_lanes:clause:3» A B C D E F input0) = SpecTec.«$num_lanes:clause:3» A B C D E F input0 := by
  unfold «$num_lanes:clause:3» SpecTec.«$num_lanes:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$num_lanes:clause:4» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) :
    erase («$num_lanes:clause:4» A B C D E F input0) = SpecTec.«$num_lanes:clause:4» A B C D E F input0 := by
  unfold «$num_lanes:clause:4» SpecTec.«$num_lanes:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$num_lanes:clause:5» (A : Type) (B : Type) (C : Type) (D : Type) (E : Type) (F : Type) (input0 : (vecop (laneop A B C D E F))) :
    erase («$num_lanes:clause:5» A B C D E F input0) = SpecTec.«$num_lanes:clause:5» A B C D E F input0 := by
  unfold «$num_lanes:clause:5» SpecTec.«$num_lanes:clause:5»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$diff_reftype:clause:0» (input0 : reftype) (input1 : reftype) :
    erase («$diff_reftype:clause:0» input0 input1) = SpecTec.«$diff_reftype:clause:0» input0 input1 := by
  unfold «$diff_reftype:clause:0» SpecTec.«$diff_reftype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$diff_reftype:clause:1» (input0 : reftype) (input1 : reftype) :
    erase («$diff_reftype:clause:1» input0 input1) = SpecTec.«$diff_reftype:clause:1» input0 input1 := by
  unfold «$diff_reftype:clause:1» SpecTec.«$diff_reftype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_null:clause:0» (input0 : SpecTec.null) (input1 : SpecTec.null) :
    erase («$match_null:clause:0» input0 input1) = SpecTec.«$match_null:clause:0» input0 input1 := by
  unfold «$match_null:clause:0» SpecTec.«$match_null:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_null:clause:1» (input0 : null) (input1 : null) :
    erase («$match_null:clause:1» input0 input1) = SpecTec.«$match_null:clause:1» input0 input1 := by
  unfold «$match_null:clause:1» SpecTec.«$match_null:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_null:clause:2» (input0 : null) (input1 : null) :
    erase («$match_null:clause:2» input0 input1) = SpecTec.«$match_null:clause:2» input0 input1 := by
  unfold «$match_null:clause:2» SpecTec.«$match_null:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_num:clause:0» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (input0 : (op A_T B_T C_T D_T)) :
    erase («$type_num:clause:0» A_T B_T C_T D_T input0) = SpecTec.«$type_num:clause:0» A_T B_T C_T D_T input0 := by
  unfold «$type_num:clause:0» SpecTec.«$type_num:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_num:clause:1» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (input0 : (op A_T B_T C_T D_T)) :
    erase («$type_num:clause:1» A_T B_T C_T D_T input0) = SpecTec.«$type_num:clause:1» A_T B_T C_T D_T input0 := by
  unfold «$type_num:clause:1» SpecTec.«$type_num:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_num:clause:2» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (input0 : (op A_T B_T C_T D_T)) :
    erase («$type_num:clause:2» A_T B_T C_T D_T input0) = SpecTec.«$type_num:clause:2» A_T B_T C_T D_T input0 := by
  unfold «$type_num:clause:2» SpecTec.«$type_num:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_num:clause:3» (A_T : Type) (B_T : Type) (C_T : Type) (D_T : Type) (input0 : (op A_T B_T C_T D_T)) :
    erase («$type_num:clause:3» A_T B_T C_T D_T input0) = SpecTec.«$type_num:clause:3» A_T B_T C_T D_T input0 := by
  unfold «$type_num:clause:3» SpecTec.«$type_num:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:0» (input0 : cvtop_) :
    erase («$type_cvtop:clause:0» input0) = SpecTec.«$type_cvtop:clause:0» input0 := by
  unfold «$type_cvtop:clause:0» SpecTec.«$type_cvtop:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:1» (input0 : cvtop_) :
    erase («$type_cvtop:clause:1» input0) = SpecTec.«$type_cvtop:clause:1» input0 := by
  unfold «$type_cvtop:clause:1» SpecTec.«$type_cvtop:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:2» (input0 : cvtop_) :
    erase («$type_cvtop:clause:2» input0) = SpecTec.«$type_cvtop:clause:2» input0 := by
  unfold «$type_cvtop:clause:2» SpecTec.«$type_cvtop:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:3» (input0 : cvtop_) :
    erase («$type_cvtop:clause:3» input0) = SpecTec.«$type_cvtop:clause:3» input0 := by
  unfold «$type_cvtop:clause:3» SpecTec.«$type_cvtop:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:4» (input0 : cvtop_) :
    erase («$type_cvtop:clause:4» input0) = SpecTec.«$type_cvtop:clause:4» input0 := by
  unfold «$type_cvtop:clause:4» SpecTec.«$type_cvtop:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:5» (input0 : cvtop_) :
    erase («$type_cvtop:clause:5» input0) = SpecTec.«$type_cvtop:clause:5» input0 := by
  unfold «$type_cvtop:clause:5» SpecTec.«$type_cvtop:clause:5»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:6» (input0 : cvtop_) :
    erase («$type_cvtop:clause:6» input0) = SpecTec.«$type_cvtop:clause:6» input0 := by
  unfold «$type_cvtop:clause:6» SpecTec.«$type_cvtop:clause:6»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:7» (input0 : cvtop_) :
    erase («$type_cvtop:clause:7» input0) = SpecTec.«$type_cvtop:clause:7» input0 := by
  unfold «$type_cvtop:clause:7» SpecTec.«$type_cvtop:clause:7»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:8» (input0 : cvtop_) :
    erase («$type_cvtop:clause:8» input0) = SpecTec.«$type_cvtop:clause:8» input0 := by
  unfold «$type_cvtop:clause:8» SpecTec.«$type_cvtop:clause:8»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:9» (input0 : cvtop_) :
    erase («$type_cvtop:clause:9» input0) = SpecTec.«$type_cvtop:clause:9» input0 := by
  unfold «$type_cvtop:clause:9» SpecTec.«$type_cvtop:clause:9»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:10» (input0 : cvtop_) :
    erase («$type_cvtop:clause:10» input0) = SpecTec.«$type_cvtop:clause:10» input0 := by
  unfold «$type_cvtop:clause:10» SpecTec.«$type_cvtop:clause:10»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$type_cvtop:clause:11» (input0 : cvtop_) :
    erase («$type_cvtop:clause:11» input0) = SpecTec.«$type_cvtop:clause:11» input0 := by
  unfold «$type_cvtop:clause:11» SpecTec.«$type_cvtop:clause:11»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$check_uop_extends:clause:0» (input0 : unop_) :
    erase («$check_uop_extends:clause:0» input0) = SpecTec.«$check_uop_extends:clause:0» input0 := by
  unfold «$check_uop_extends:clause:0» SpecTec.«$check_uop_extends:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$check_uop_extends:clause:1» (input0 : unop_) :
    erase («$check_uop_extends:clause:1» input0) = SpecTec.«$check_uop_extends:clause:1» input0 := by
  unfold «$check_uop_extends:clause:1» SpecTec.«$check_uop_extends:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$check_uop_extends:clause:2» (input0 : unop_) :
    erase («$check_uop_extends:clause:2» input0) = SpecTec.«$check_uop_extends:clause:2» input0 := by
  unfold «$check_uop_extends:clause:2» SpecTec.«$check_uop_extends:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$pack_size:clause:0» (input0 : packtype) :
    erase («$pack_size:clause:0» input0) = SpecTec.«$pack_size:clause:0» input0 := by
  unfold «$pack_size:clause:0» SpecTec.«$pack_size:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$pack_size:clause:1» (input0 : packtype) :
    erase («$pack_size:clause:1» input0) = SpecTec.«$pack_size:clause:1» input0 := by
  unfold «$pack_size:clause:1» SpecTec.«$pack_size:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$pack_size:clause:2» (input0 : packtype) :
    erase («$pack_size:clause:2» input0) = SpecTec.«$pack_size:clause:2» input0 := by
  unfold «$pack_size:clause:2» SpecTec.«$pack_size:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$pack_size:clause:3» (input0 : packtype) :
    erase («$pack_size:clause:3» input0) = SpecTec.«$pack_size:clause:3» input0 := by
  unfold «$pack_size:clause:3» SpecTec.«$pack_size:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Pack_ok:clause:0» (input0 : _root_.Int) (input1 : SpecTec.packtype) :
    erase («Pack_ok:clause:0» input0 input1) = SpecTec.«Pack_ok:clause:0» input0 input1 := by
  unfold «Pack_ok:clause:0» SpecTec.«Pack_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Unop_ok:clause:0» (input0 : unop_) :
    erase («Unop_ok:clause:0» input0) = SpecTec.«Unop_ok:clause:0» input0 := by
  unfold «Unop_ok:clause:0» SpecTec.«Unop_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Unop_ok:clause:1» (input0 : unop_) :
    erase («Unop_ok:clause:1» input0) = SpecTec.«Unop_ok:clause:1» input0 := by
  unfold «Unop_ok:clause:1» SpecTec.«Unop_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Unop_ok:clause:2» (input0 : unop_) :
    erase («Unop_ok:clause:2» input0) = SpecTec.«Unop_ok:clause:2» input0 := by
  unfold «Unop_ok:clause:2» SpecTec.«Unop_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Loadop_ok:clause:0» (input0 : context) (input1 : loadop_) :
    erase («Loadop_ok:clause:0» input0 input1) = SpecTec.«Loadop_ok:clause:0» input0 input1 := by
  unfold «Loadop_ok:clause:0» SpecTec.«Loadop_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Loadop_ok:clause:1» (input0 : context) (input1 : loadop_) :
    erase («Loadop_ok:clause:1» input0 input1) = SpecTec.«Loadop_ok:clause:1» input0 input1 := by
  unfold «Loadop_ok:clause:1» SpecTec.«Loadop_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Loadop_ok:clause:2» (input0 : context) (input1 : loadop_) :
    erase («Loadop_ok:clause:2» input0 input1) = SpecTec.«Loadop_ok:clause:2» input0 input1 := by
  unfold «Loadop_ok:clause:2» SpecTec.«Loadop_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Loadop_ok:clause:3» (input0 : context) (input1 : loadop_) :
    erase («Loadop_ok:clause:3» input0 input1) = SpecTec.«Loadop_ok:clause:3» input0 input1 := by
  unfold «Loadop_ok:clause:3» SpecTec.«Loadop_ok:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Storeop_ok:clause:0» (input0 : context) (input1 : storeop_) :
    erase («Storeop_ok:clause:0» input0 input1) = SpecTec.«Storeop_ok:clause:0» input0 input1 := by
  unfold «Storeop_ok:clause:0» SpecTec.«Storeop_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Storeop_ok:clause:1» (input0 : context) (input1 : storeop_) :
    erase («Storeop_ok:clause:1» input0 input1) = SpecTec.«Storeop_ok:clause:1» input0 input1 := by
  unfold «Storeop_ok:clause:1» SpecTec.«Storeop_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Storeop_ok:clause:2» (input0 : context) (input1 : storeop_) :
    erase («Storeop_ok:clause:2» input0 input1) = SpecTec.«Storeop_ok:clause:2» input0 input1 := by
  unfold «Storeop_ok:clause:2» SpecTec.«Storeop_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Storeop_ok:clause:3» (input0 : context) (input1 : storeop_) :
    erase («Storeop_ok:clause:3» input0 input1) = SpecTec.«Storeop_ok:clause:3» input0 input1 := by
  unfold «Storeop_ok:clause:3» SpecTec.«Storeop_ok:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Vloadop_ok:clause:0» (input0 : context) (input1 : vloadop_) :
    erase («Vloadop_ok:clause:0» input0 input1) = SpecTec.«Vloadop_ok:clause:0» input0 input1 := by
  unfold «Vloadop_ok:clause:0» SpecTec.«Vloadop_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Vloadop_ok:clause:1» (input0 : context) (input1 : vloadop_) :
    erase («Vloadop_ok:clause:1» input0 input1) = SpecTec.«Vloadop_ok:clause:1» input0 input1 := by
  unfold «Vloadop_ok:clause:1» SpecTec.«Vloadop_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Vloadop_ok:clause:2» (input0 : context) (input1 : vloadop_) :
    erase («Vloadop_ok:clause:2» input0 input1) = SpecTec.«Vloadop_ok:clause:2» input0 input1 := by
  unfold «Vloadop_ok:clause:2» SpecTec.«Vloadop_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Vloadop_ok:clause:3» (input0 : context) (input1 : vloadop_) :
    erase («Vloadop_ok:clause:3» input0 input1) = SpecTec.«Vloadop_ok:clause:3» input0 input1 := by
  unfold «Vloadop_ok:clause:3» SpecTec.«Vloadop_ok:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Vlaneop_ok:clause:0» (input0 : context) (input1 : vlaneop_) :
    erase («Vlaneop_ok:clause:0» input0 input1) = SpecTec.«Vlaneop_ok:clause:0» input0 input1 := by
  unfold «Vlaneop_ok:clause:0» SpecTec.«Vlaneop_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Vlaneop_ok:clause:1» (input0 : context) (input1 : vlaneop_) :
    erase («Vlaneop_ok:clause:1» input0 input1) = SpecTec.«Vlaneop_ok:clause:1» input0 input1 := by
  unfold «Vlaneop_ok:clause:1» SpecTec.«Vlaneop_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$unpacked_storage_type:clause:0» (input0 : storagetype) :
    erase («$unpacked_storage_type:clause:0» input0) = SpecTec.«$unpacked_storage_type:clause:0» input0 := by
  unfold «$unpacked_storage_type:clause:0» SpecTec.«$unpacked_storage_type:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$unpacked_storage_type:clause:1» (input0 : storagetype) :
    erase («$unpacked_storage_type:clause:1» input0) = SpecTec.«$unpacked_storage_type:clause:1» input0 := by
  unfold «$unpacked_storage_type:clause:1» SpecTec.«$unpacked_storage_type:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$unpacked_field_type:clause:0» (input0 : fieldtype) :
    erase («$unpacked_field_type:clause:0» input0) = SpecTec.«$unpacked_field_type:clause:0» input0 := by
  unfold «$unpacked_field_type:clause:0» SpecTec.«$unpacked_field_type:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_packed_storage_type:clause:0» (input0 : storagetype) :
    erase («$is_packed_storage_type:clause:0» input0) = SpecTec.«$is_packed_storage_type:clause:0» input0 := by
  unfold «$is_packed_storage_type:clause:0» SpecTec.«$is_packed_storage_type:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_packed_storage_type:clause:1» (input0 : storagetype) :
    erase («$is_packed_storage_type:clause:1» input0) = SpecTec.«$is_packed_storage_type:clause:1» input0 := by
  unfold «$is_packed_storage_type:clause:1» SpecTec.«$is_packed_storage_type:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:struct.new.explicit:iter:1:clause:0» (input0 : (_root_.List fieldtype)) :
    erase («Instr_ok:struct.new.explicit:iter:1:clause:0» input0) = SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:0» input0 := by
  unfold «Instr_ok:struct.new.explicit:iter:1:clause:0» SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:struct.new.explicit:iter:1:clause:1» (input0 : (_root_.List fieldtype)) :
    erase («Instr_ok:struct.new.explicit:iter:1:clause:1» input0) = SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:1» input0 := by
  unfold «Instr_ok:struct.new.explicit:iter:1:clause:1» SpecTec.«Instr_ok:struct.new.explicit:iter:1:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$functype_of_strtype:clause:0» (input0 : strtype) :
    erase («$functype_of_strtype:clause:0» input0) = SpecTec.«$functype_of_strtype:clause:0» input0 := by
  unfold «$functype_of_strtype:clause:0» SpecTec.«$functype_of_strtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$abs_of_str_type:clause:0» (input0 : strtype) :
    erase («$abs_of_str_type:clause:0» input0) = SpecTec.«$abs_of_str_type:clause:0» input0 := by
  unfold «$abs_of_str_type:clause:0» SpecTec.«$abs_of_str_type:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$abs_of_str_type:clause:1» (input0 : strtype) :
    erase («$abs_of_str_type:clause:1» input0) = SpecTec.«$abs_of_str_type:clause:1» input0 := by
  unfold «$abs_of_str_type:clause:1» SpecTec.«$abs_of_str_type:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$abs_of_str_type:clause:2» (input0 : strtype) :
    erase («$abs_of_str_type:clause:2» input0) = SpecTec.«$abs_of_str_type:clause:2» input0 := by
  unfold «$abs_of_str_type:clause:2» SpecTec.«$abs_of_str_type:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$s_unroll:clause:0» (input0 : typevar) (input1 : rectype) :
    erase («$s_unroll:clause:0» input0 input1) = SpecTec.«$s_unroll:clause:0» input0 input1 := by
  unfold «$s_unroll:clause:0» SpecTec.«$s_unroll:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$s_unroll:clause:1» (input0 : typevar) (input1 : rectype) :
    erase («$s_unroll:clause:1» input0 input1) = SpecTec.«$s_unroll:clause:1» input0 input1 := by
  unfold «$s_unroll:clause:1» SpecTec.«$s_unroll:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$s_roll:clause:0» (input0 : typevar) (input1 : (typeidx × typeidx)) :
    erase («$s_roll:clause:0» input0 input1) = SpecTec.«$s_roll:clause:0» input0 input1 := by
  unfold «$s_roll:clause:0» SpecTec.«$s_roll:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$s_roll:clause:1» (input0 : typevar) (input1 : (typeidx × typeidx)) :
    erase («$s_roll:clause:1» input0 input1) = SpecTec.«$s_roll:clause:1» input0 input1 := by
  unfold «$s_roll:clause:1» SpecTec.«$s_roll:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_typevar:clause:0» (input0 : typevar) :
    erase («$free_typevar:clause:0» input0) = SpecTec.«$free_typevar:clause:0» input0 := by
  unfold «$free_typevar:clause:0» SpecTec.«$free_typevar:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_typevar:clause:1» (input0 : typevar) :
    erase («$free_typevar:clause:1» input0) = SpecTec.«$free_typevar:clause:1» input0 := by
  unfold «$free_typevar:clause:1» SpecTec.«$free_typevar:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_of:clause:0» (input0 : typevar) (input1 : (_root_.List deftype)) :
    erase («$subst_of:clause:0» input0 input1) = SpecTec.«$subst_of:clause:0» input0 input1 := by
  unfold «$subst_of:clause:0» SpecTec.«$subst_of:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_of:clause:1» (input0 : typevar) (input1 : (_root_.List deftype)) :
    erase («$subst_of:clause:1» input0 input1) = SpecTec.«$subst_of:clause:1» input0 input1 := by
  unfold «$subst_of:clause:1» SpecTec.«$subst_of:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_num_type:clause:0» (input0 : SpecTec.valtype) :
    erase («$is_num_type:clause:0» input0) = SpecTec.«$is_num_type:clause:0» input0 := by
  unfold «$is_num_type:clause:0» SpecTec.«$is_num_type:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_num_type:clause:1» (input0 : SpecTec.valtype) :
    erase («$is_num_type:clause:1» input0) = SpecTec.«$is_num_type:clause:1» input0 := by
  unfold «$is_num_type:clause:1» SpecTec.«$is_num_type:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_num_type:clause:2» (input0 : valtype) :
    erase («$is_num_type:clause:2» input0) = SpecTec.«$is_num_type:clause:2» input0 := by
  unfold «$is_num_type:clause:2» SpecTec.«$is_num_type:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$peek_ref:clause:0» (input0 : _root_.Nat) (input1 : inferresulttype) :
    erase («$peek_ref:clause:0» input0 input1) = SpecTec.«$peek_ref:clause:0» input0 input1 := by
  unfold «$peek_ref:clause:0» SpecTec.«$peek_ref:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$peek_ref:clause:1» (input0 : _root_.Nat) (input1 : inferresulttype) :
    erase («$peek_ref:clause:1» input0 input1) = SpecTec.«$peek_ref:clause:1» input0 input1 := by
  unfold «$peek_ref:clause:1» SpecTec.«$peek_ref:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_vec_type:clause:0» (input0 : SpecTec.valtype) :
    erase («$is_vec_type:clause:0» input0) = SpecTec.«$is_vec_type:clause:0» input0 := by
  unfold «$is_vec_type:clause:0» SpecTec.«$is_vec_type:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_vec_type:clause:1» (input0 : SpecTec.valtype) :
    erase («$is_vec_type:clause:1» input0) = SpecTec.«$is_vec_type:clause:1» input0 := by
  unfold «$is_vec_type:clause:1» SpecTec.«$is_vec_type:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$is_vec_type:clause:2» (input0 : valtype) :
    erase («$is_vec_type:clause:2» input0) = SpecTec.«$is_vec_type:clause:2» input0 := by
  unfold «$is_vec_type:clause:2» SpecTec.«$is_vec_type:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$defaultable:clause:0» (input0 : SpecTec.valtype) :
    erase («$defaultable:clause:0» input0) = SpecTec.«$defaultable:clause:0» input0 := by
  unfold «$defaultable:clause:0» SpecTec.«$defaultable:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$defaultable:clause:1» (input0 : SpecTec.valtype) :
    erase («$defaultable:clause:1» input0) = SpecTec.«$defaultable:clause:1» input0 := by
  unfold «$defaultable:clause:1» SpecTec.«$defaultable:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$defaultable:clause:2» (input0 : SpecTec.valtype) :
    erase («$defaultable:clause:2» input0) = SpecTec.«$defaultable:clause:2» input0 := by
  unfold «$defaultable:clause:2» SpecTec.«$defaultable:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$defaultable:clause:3» (input0 : SpecTec.valtype) :
    erase («$defaultable:clause:3» input0) = SpecTec.«$defaultable:clause:3» input0 := by
  unfold «$defaultable:clause:3» SpecTec.«$defaultable:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:struct.new.implicit:iter:1:clause:0» (input0 : (_root_.List fieldtype)) :
    erase («Instr_ok:struct.new.implicit:iter:1:clause:0» input0) = SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:0» input0 := by
  unfold «Instr_ok:struct.new.implicit:iter:1:clause:0» SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:struct.new.implicit:iter:1:clause:1» (input0 : (_root_.List fieldtype)) :
    erase («Instr_ok:struct.new.implicit:iter:1:clause:1» input0) = SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:1» input0 := by
  unfold «Instr_ok:struct.new.implicit:iter:1:clause:1» SpecTec.«Instr_ok:struct.new.implicit:iter:1:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$check_vbop_shuffle:clause:0» (input0 : vbinop_) :
    erase («$check_vbop_shuffle:clause:0» input0) = SpecTec.«$check_vbop_shuffle:clause:0» input0 := by
  unfold «$check_vbop_shuffle:clause:0» SpecTec.«$check_vbop_shuffle:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$check_vbop_shuffle:clause:1» (input0 : vbinop_) :
    erase («$check_vbop_shuffle:clause:1» input0) = SpecTec.«$check_vbop_shuffle:clause:1» input0 := by
  unfold «$check_vbop_shuffle:clause:1» SpecTec.«$check_vbop_shuffle:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Vecbinop_ok:clause:0» (input0 : vbinop_) :
    erase («Vecbinop_ok:clause:0» input0) = SpecTec.«Vecbinop_ok:clause:0» input0 := by
  unfold «Vecbinop_ok:clause:0» SpecTec.«Vecbinop_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Vecbinop_ok:clause:1» (input0 : vbinop_) :
    erase («Vecbinop_ok:clause:1» input0) = SpecTec.«Vecbinop_ok:clause:1» input0 := by
  unfold «Vecbinop_ok:clause:1» SpecTec.«Vecbinop_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_heaptype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : heaptype) :
    erase («$subst_heaptype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_heaptype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_heaptype:clause:0» SpecTec.«$subst_heaptype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_heaptype:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : heaptype) :
    erase («$subst_heaptype:clause:1» X_T input0 input1 input2) = SpecTec.«$subst_heaptype:clause:1» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_heaptype:clause:1» SpecTec.«$subst_heaptype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_heaptype:clause:2» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : heaptype) :
    erase («$subst_heaptype:clause:2» X_T input0 input1 input2) = SpecTec.«$subst_heaptype:clause:2» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_heaptype:clause:2» SpecTec.«$subst_heaptype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_subtype:case_1:iter:0:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List heaptype)) :
    erase («$subst_subtype:case_1:iter:0:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_subtype:case_1:iter:0:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_subtype:case_1:iter:0:clause:0» SpecTec.«$subst_subtype:case_1:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_subtype:case_1:iter:0:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List heaptype)) :
    erase («$subst_subtype:case_1:iter:0:clause:1» X_T input0 input1 input2) = SpecTec.«$subst_subtype:case_1:iter:0:clause:1» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_subtype:case_1:iter:0:clause:1» SpecTec.«$subst_subtype:case_1:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_reftype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : reftype) :
    erase («$subst_reftype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_reftype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_reftype:clause:0» SpecTec.«$subst_reftype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_valtype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : SpecTec.valtype) :
    erase («$subst_valtype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_valtype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_valtype:clause:0» SpecTec.«$subst_valtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_valtype:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : SpecTec.valtype) :
    erase («$subst_valtype:clause:1» X_T input0 input1 input2) = SpecTec.«$subst_valtype:clause:1» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_valtype:clause:1» SpecTec.«$subst_valtype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_valtype:clause:2» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : SpecTec.valtype) :
    erase («$subst_valtype:clause:2» X_T input0 input1 input2) = SpecTec.«$subst_valtype:clause:2» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_valtype:clause:2» SpecTec.«$subst_valtype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_valtype:clause:3» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : valtype) :
    erase («$subst_valtype:clause:3» X_T input0 input1 input2) = SpecTec.«$subst_valtype:clause:3» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_valtype:clause:3» SpecTec.«$subst_valtype:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_resulttype:case_1:iter:0:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List valtype)) :
    erase («$subst_resulttype:case_1:iter:0:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_resulttype:case_1:iter:0:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_resulttype:case_1:iter:0:clause:0» SpecTec.«$subst_resulttype:case_1:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_resulttype:case_1:iter:0:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List valtype)) :
    erase («$subst_resulttype:case_1:iter:0:clause:1» X_T input0 input1 input2) = SpecTec.«$subst_resulttype:case_1:iter:0:clause:1» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_resulttype:case_1:iter:0:clause:1» SpecTec.«$subst_resulttype:case_1:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_resulttype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : resulttype) :
    erase («$subst_resulttype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_resulttype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_resulttype:clause:0» SpecTec.«$subst_resulttype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_functype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : functype) :
    erase («$subst_functype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_functype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_functype:clause:0» SpecTec.«$subst_functype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_storagetype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : storagetype) :
    erase («$subst_storagetype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_storagetype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_storagetype:clause:0» SpecTec.«$subst_storagetype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_storagetype:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : storagetype) :
    erase («$subst_storagetype:clause:1» X_T input0 input1 input2) = SpecTec.«$subst_storagetype:clause:1» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_storagetype:clause:1» SpecTec.«$subst_storagetype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_fieldtype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : fieldtype) :
    erase («$subst_fieldtype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_fieldtype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_fieldtype:clause:0» SpecTec.«$subst_fieldtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_structtype:case_1:iter:0:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List fieldtype)) :
    erase («$subst_structtype:case_1:iter:0:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_structtype:case_1:iter:0:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_structtype:case_1:iter:0:clause:0» SpecTec.«$subst_structtype:case_1:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_structtype:case_1:iter:0:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List fieldtype)) :
    erase («$subst_structtype:case_1:iter:0:clause:1» X_T input0 input1 input2) = SpecTec.«$subst_structtype:case_1:iter:0:clause:1» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_structtype:case_1:iter:0:clause:1» SpecTec.«$subst_structtype:case_1:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_structtype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : structtype) :
    erase («$subst_structtype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_structtype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_structtype:clause:0» SpecTec.«$subst_structtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_arraytype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : arraytype) :
    erase («$subst_arraytype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_arraytype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_arraytype:clause:0» SpecTec.«$subst_arraytype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_strtype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : strtype) :
    erase («$subst_strtype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_strtype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_strtype:clause:0» SpecTec.«$subst_strtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_strtype:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : strtype) :
    erase («$subst_strtype:clause:1» X_T input0 input1 input2) = SpecTec.«$subst_strtype:clause:1» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_strtype:clause:1» SpecTec.«$subst_strtype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_strtype:clause:2» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : strtype) :
    erase («$subst_strtype:clause:2» X_T input0 input1 input2) = SpecTec.«$subst_strtype:clause:2» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_strtype:clause:2» SpecTec.«$subst_strtype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_subtype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : subtype) :
    erase («$subst_subtype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_subtype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_subtype:clause:0» SpecTec.«$subst_subtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_rectype:case_1:iter:0:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List subtype)) :
    erase («$subst_rectype:case_1:iter:0:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_rectype:case_1:iter:0:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_rectype:case_1:iter:0:clause:0» SpecTec.«$subst_rectype:case_1:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_rectype:case_1:iter:0:clause:1» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : (_root_.List subtype)) :
    erase («$subst_rectype:case_1:iter:0:clause:1» X_T input0 input1 input2) = SpecTec.«$subst_rectype:case_1:iter:0:clause:1» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_rectype:case_1:iter:0:clause:1» SpecTec.«$subst_rectype:case_1:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_rectype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : rectype) :
    erase («$subst_rectype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_rectype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_rectype:clause:0» SpecTec.«$subst_rectype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$subst_deftype:clause:0» (X_T : Type) (input0 : X_T) (input1 : (typevar → X_T → (Call heaptype))) (input2 : deftype) :
    erase («$subst_deftype:clause:0» X_T input0 input1 input2) = SpecTec.«$subst_deftype:clause:0» X_T input0 (fun v0 v1 => toOriginal (input1 v0 v1)) input2 := by
  unfold «$subst_deftype:clause:0» SpecTec.«$subst_deftype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$rollrt:clause:0» (input0 : typeidx) (input1 : rectype) :
    erase («$rollrt:clause:0» input0 input1) = SpecTec.«$rollrt:clause:0» input0 input1 := by
  unfold «$rollrt:clause:0» SpecTec.«$rollrt:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$unrollrt:clause:0» (input0 : rectype) :
    erase («$unrollrt:clause:0» input0) = SpecTec.«$unrollrt:clause:0» input0 := by
  unfold «$unrollrt:clause:0» SpecTec.«$unrollrt:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$rolldt:clause:0» (input0 : typeidx) (input1 : rectype) :
    erase («$rolldt:clause:0» input0 input1) = SpecTec.«$rolldt:clause:0» input0 input1 := by
  unfold «$rolldt:clause:0» SpecTec.«$rolldt:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$unrolldt:clause:0» (input0 : deftype) :
    erase («$unrolldt:clause:0» input0) = SpecTec.«$unrolldt:clause:0» input0 := by
  unfold «$unrolldt:clause:0» SpecTec.«$unrolldt:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$expanddt:clause:0» (input0 : deftype) :
    erase («$expanddt:clause:0» input0) = SpecTec.«$expanddt:clause:0» input0 := by
  unfold «$expanddt:clause:0» SpecTec.«$expanddt:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_heaptype:clause:0» (input0 : heaptype) :
    erase («$free_heaptype:clause:0» input0) = SpecTec.«$free_heaptype:clause:0» input0 := by
  unfold «$free_heaptype:clause:0» SpecTec.«$free_heaptype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_heaptype:clause:1» (input0 : heaptype) :
    erase («$free_heaptype:clause:1» input0) = SpecTec.«$free_heaptype:clause:1» input0 := by
  unfold «$free_heaptype:clause:1» SpecTec.«$free_heaptype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_reftype:clause:0» (input0 : reftype) :
    erase («$free_reftype:clause:0» input0) = SpecTec.«$free_reftype:clause:0» input0 := by
  unfold «$free_reftype:clause:0» SpecTec.«$free_reftype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_valtype:clause:0» (input0 : SpecTec.valtype) :
    erase («$free_valtype:clause:0» input0) = SpecTec.«$free_valtype:clause:0» input0 := by
  unfold «$free_valtype:clause:0» SpecTec.«$free_valtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_valtype:clause:1» (input0 : SpecTec.valtype) :
    erase («$free_valtype:clause:1» input0) = SpecTec.«$free_valtype:clause:1» input0 := by
  unfold «$free_valtype:clause:1» SpecTec.«$free_valtype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_valtype:clause:2» (input0 : SpecTec.valtype) :
    erase («$free_valtype:clause:2» input0) = SpecTec.«$free_valtype:clause:2» input0 := by
  unfold «$free_valtype:clause:2» SpecTec.«$free_valtype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_valtype:clause:3» (input0 : SpecTec.valtype) :
    erase («$free_valtype:clause:3» input0) = SpecTec.«$free_valtype:clause:3» input0 := by
  unfold «$free_valtype:clause:3» SpecTec.«$free_valtype:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_functype:clause:0» (input0 : functype) :
    erase («$free_functype:clause:0» input0) = SpecTec.«$free_functype:clause:0» input0 := by
  unfold «$free_functype:clause:0» SpecTec.«$free_functype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_storagetype:clause:0» (input0 : storagetype) :
    erase («$free_storagetype:clause:0» input0) = SpecTec.«$free_storagetype:clause:0» input0 := by
  unfold «$free_storagetype:clause:0» SpecTec.«$free_storagetype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_storagetype:clause:1» (input0 : storagetype) :
    erase («$free_storagetype:clause:1» input0) = SpecTec.«$free_storagetype:clause:1» input0 := by
  unfold «$free_storagetype:clause:1» SpecTec.«$free_storagetype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_fieldtype:clause:0» (input0 : fieldtype) :
    erase («$free_fieldtype:clause:0» input0) = SpecTec.«$free_fieldtype:clause:0» input0 := by
  unfold «$free_fieldtype:clause:0» SpecTec.«$free_fieldtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_structtype:clause:0» (input0 : structtype) :
    erase («$free_structtype:clause:0» input0) = SpecTec.«$free_structtype:clause:0» input0 := by
  unfold «$free_structtype:clause:0» SpecTec.«$free_structtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_arraytype:clause:0» (input0 : arraytype) :
    erase («$free_arraytype:clause:0» input0) = SpecTec.«$free_arraytype:clause:0» input0 := by
  unfold «$free_arraytype:clause:0» SpecTec.«$free_arraytype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_strtype:clause:0» (input0 : strtype) :
    erase («$free_strtype:clause:0» input0) = SpecTec.«$free_strtype:clause:0» input0 := by
  unfold «$free_strtype:clause:0» SpecTec.«$free_strtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_strtype:clause:1» (input0 : strtype) :
    erase («$free_strtype:clause:1» input0) = SpecTec.«$free_strtype:clause:1» input0 := by
  unfold «$free_strtype:clause:1» SpecTec.«$free_strtype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_strtype:clause:2» (input0 : strtype) :
    erase («$free_strtype:clause:2» input0) = SpecTec.«$free_strtype:clause:2» input0 := by
  unfold «$free_strtype:clause:2» SpecTec.«$free_strtype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_subtype:clause:0» (input0 : subtype) :
    erase («$free_subtype:clause:0» input0) = SpecTec.«$free_subtype:clause:0» input0 := by
  unfold «$free_subtype:clause:0» SpecTec.«$free_subtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_rectype:clause:0» (input0 : rectype) :
    erase («$free_rectype:clause:0» input0) = SpecTec.«$free_rectype:clause:0» input0 := by
  unfold «$free_rectype:clause:0» SpecTec.«$free_rectype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_type_:clause:0» (input0 : SpecTec.type) :
    erase («$free_type_:clause:0» input0) = SpecTec.«$free_type_:clause:0» input0 := by
  unfold «$free_type_:clause:0» SpecTec.«$free_type_:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_globaltype:clause:0» (input0 : globaltype) :
    erase («$free_globaltype:clause:0» input0) = SpecTec.«$free_globaltype:clause:0» input0 := by
  unfold «$free_globaltype:clause:0» SpecTec.«$free_globaltype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_blocktype:clause:0» (input0 : SpecTec.blocktype) :
    erase («$free_blocktype:clause:0» input0) = SpecTec.«$free_blocktype:clause:0» input0 := by
  unfold «$free_blocktype:clause:0» SpecTec.«$free_blocktype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_blocktype:clause:1» (input0 : SpecTec.blocktype) :
    erase («$free_blocktype:clause:1» input0) = SpecTec.«$free_blocktype:clause:1» input0 := by
  unfold «$free_blocktype:clause:1» SpecTec.«$free_blocktype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_blocktype:clause:2» (input0 : SpecTec.blocktype) :
    erase («$free_blocktype:clause:2» input0) = SpecTec.«$free_blocktype:clause:2» input0 := by
  unfold «$free_blocktype:clause:2» SpecTec.«$free_blocktype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:0» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:0» input0) = SpecTec.«$free_instr:clause:0» input0 := by
  unfold «$free_instr:clause:0» SpecTec.«$free_instr:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:1» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:1» input0) = SpecTec.«$free_instr:clause:1» input0 := by
  unfold «$free_instr:clause:1» SpecTec.«$free_instr:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:2» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:2» input0) = SpecTec.«$free_instr:clause:2» input0 := by
  unfold «$free_instr:clause:2» SpecTec.«$free_instr:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:3» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:3» input0) = SpecTec.«$free_instr:clause:3» input0 := by
  unfold «$free_instr:clause:3» SpecTec.«$free_instr:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:4» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:4» input0) = SpecTec.«$free_instr:clause:4» input0 := by
  unfold «$free_instr:clause:4» SpecTec.«$free_instr:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:5» (input0 : instr) :
    erase («$free_instr:clause:5» input0) = SpecTec.«$free_instr:clause:5» input0 := by
  unfold «$free_instr:clause:5» SpecTec.«$free_instr:clause:5»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:6» (input0 : instr) :
    erase («$free_instr:clause:6» input0) = SpecTec.«$free_instr:clause:6» input0 := by
  unfold «$free_instr:clause:6» SpecTec.«$free_instr:clause:6»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:7» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:7» input0) = SpecTec.«$free_instr:clause:7» input0 := by
  unfold «$free_instr:clause:7» SpecTec.«$free_instr:clause:7»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:8» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:8» input0) = SpecTec.«$free_instr:clause:8» input0 := by
  unfold «$free_instr:clause:8» SpecTec.«$free_instr:clause:8»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:9» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:9» input0) = SpecTec.«$free_instr:clause:9» input0 := by
  unfold «$free_instr:clause:9» SpecTec.«$free_instr:clause:9»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:10» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:10» input0) = SpecTec.«$free_instr:clause:10» input0 := by
  unfold «$free_instr:clause:10» SpecTec.«$free_instr:clause:10»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:11» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:11» input0) = SpecTec.«$free_instr:clause:11» input0 := by
  unfold «$free_instr:clause:11» SpecTec.«$free_instr:clause:11»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:12» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:12» input0) = SpecTec.«$free_instr:clause:12» input0 := by
  unfold «$free_instr:clause:12» SpecTec.«$free_instr:clause:12»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:13» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:13» input0) = SpecTec.«$free_instr:clause:13» input0 := by
  unfold «$free_instr:clause:13» SpecTec.«$free_instr:clause:13»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:14» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:14» input0) = SpecTec.«$free_instr:clause:14» input0 := by
  unfold «$free_instr:clause:14» SpecTec.«$free_instr:clause:14»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:15» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:15» input0) = SpecTec.«$free_instr:clause:15» input0 := by
  unfold «$free_instr:clause:15» SpecTec.«$free_instr:clause:15»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:16» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:16» input0) = SpecTec.«$free_instr:clause:16» input0 := by
  unfold «$free_instr:clause:16» SpecTec.«$free_instr:clause:16»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:17» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:17» input0) = SpecTec.«$free_instr:clause:17» input0 := by
  unfold «$free_instr:clause:17» SpecTec.«$free_instr:clause:17»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:18» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:18» input0) = SpecTec.«$free_instr:clause:18» input0 := by
  unfold «$free_instr:clause:18» SpecTec.«$free_instr:clause:18»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:19» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:19» input0) = SpecTec.«$free_instr:clause:19» input0 := by
  unfold «$free_instr:clause:19» SpecTec.«$free_instr:clause:19»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:20» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:20» input0) = SpecTec.«$free_instr:clause:20» input0 := by
  unfold «$free_instr:clause:20» SpecTec.«$free_instr:clause:20»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:21» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:21» input0) = SpecTec.«$free_instr:clause:21» input0 := by
  unfold «$free_instr:clause:21» SpecTec.«$free_instr:clause:21»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:22» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:22» input0) = SpecTec.«$free_instr:clause:22» input0 := by
  unfold «$free_instr:clause:22» SpecTec.«$free_instr:clause:22»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:23» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:23» input0) = SpecTec.«$free_instr:clause:23» input0 := by
  unfold «$free_instr:clause:23» SpecTec.«$free_instr:clause:23»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:24» (input0 : instr) :
    erase («$free_instr:clause:24» input0) = SpecTec.«$free_instr:clause:24» input0 := by
  unfold «$free_instr:clause:24» SpecTec.«$free_instr:clause:24»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:25» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:25» input0) = SpecTec.«$free_instr:clause:25» input0 := by
  unfold «$free_instr:clause:25» SpecTec.«$free_instr:clause:25»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:26» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:26» input0) = SpecTec.«$free_instr:clause:26» input0 := by
  unfold «$free_instr:clause:26» SpecTec.«$free_instr:clause:26»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:27» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:27» input0) = SpecTec.«$free_instr:clause:27» input0 := by
  unfold «$free_instr:clause:27» SpecTec.«$free_instr:clause:27»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:28» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:28» input0) = SpecTec.«$free_instr:clause:28» input0 := by
  unfold «$free_instr:clause:28» SpecTec.«$free_instr:clause:28»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:29» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:29» input0) = SpecTec.«$free_instr:clause:29» input0 := by
  unfold «$free_instr:clause:29» SpecTec.«$free_instr:clause:29»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:30» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:30» input0) = SpecTec.«$free_instr:clause:30» input0 := by
  unfold «$free_instr:clause:30» SpecTec.«$free_instr:clause:30»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:31» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:31» input0) = SpecTec.«$free_instr:clause:31» input0 := by
  unfold «$free_instr:clause:31» SpecTec.«$free_instr:clause:31»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:32» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:32» input0) = SpecTec.«$free_instr:clause:32» input0 := by
  unfold «$free_instr:clause:32» SpecTec.«$free_instr:clause:32»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:33» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:33» input0) = SpecTec.«$free_instr:clause:33» input0 := by
  unfold «$free_instr:clause:33» SpecTec.«$free_instr:clause:33»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:34» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:34» input0) = SpecTec.«$free_instr:clause:34» input0 := by
  unfold «$free_instr:clause:34» SpecTec.«$free_instr:clause:34»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:35» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:35» input0) = SpecTec.«$free_instr:clause:35» input0 := by
  unfold «$free_instr:clause:35» SpecTec.«$free_instr:clause:35»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:36» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:36» input0) = SpecTec.«$free_instr:clause:36» input0 := by
  unfold «$free_instr:clause:36» SpecTec.«$free_instr:clause:36»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:37» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:37» input0) = SpecTec.«$free_instr:clause:37» input0 := by
  unfold «$free_instr:clause:37» SpecTec.«$free_instr:clause:37»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:38» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:38» input0) = SpecTec.«$free_instr:clause:38» input0 := by
  unfold «$free_instr:clause:38» SpecTec.«$free_instr:clause:38»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:39» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:39» input0) = SpecTec.«$free_instr:clause:39» input0 := by
  unfold «$free_instr:clause:39» SpecTec.«$free_instr:clause:39»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:40» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:40» input0) = SpecTec.«$free_instr:clause:40» input0 := by
  unfold «$free_instr:clause:40» SpecTec.«$free_instr:clause:40»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:41» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:41» input0) = SpecTec.«$free_instr:clause:41» input0 := by
  unfold «$free_instr:clause:41» SpecTec.«$free_instr:clause:41»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:42» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:42» input0) = SpecTec.«$free_instr:clause:42» input0 := by
  unfold «$free_instr:clause:42» SpecTec.«$free_instr:clause:42»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:43» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:43» input0) = SpecTec.«$free_instr:clause:43» input0 := by
  unfold «$free_instr:clause:43» SpecTec.«$free_instr:clause:43»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:44» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:44» input0) = SpecTec.«$free_instr:clause:44» input0 := by
  unfold «$free_instr:clause:44» SpecTec.«$free_instr:clause:44»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:45» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:45» input0) = SpecTec.«$free_instr:clause:45» input0 := by
  unfold «$free_instr:clause:45» SpecTec.«$free_instr:clause:45»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:46» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:46» input0) = SpecTec.«$free_instr:clause:46» input0 := by
  unfold «$free_instr:clause:46» SpecTec.«$free_instr:clause:46»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:47» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:47» input0) = SpecTec.«$free_instr:clause:47» input0 := by
  unfold «$free_instr:clause:47» SpecTec.«$free_instr:clause:47»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:48» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:48» input0) = SpecTec.«$free_instr:clause:48» input0 := by
  unfold «$free_instr:clause:48» SpecTec.«$free_instr:clause:48»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:49» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:49» input0) = SpecTec.«$free_instr:clause:49» input0 := by
  unfold «$free_instr:clause:49» SpecTec.«$free_instr:clause:49»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:50» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:50» input0) = SpecTec.«$free_instr:clause:50» input0 := by
  unfold «$free_instr:clause:50» SpecTec.«$free_instr:clause:50»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:51» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:51» input0) = SpecTec.«$free_instr:clause:51» input0 := by
  unfold «$free_instr:clause:51» SpecTec.«$free_instr:clause:51»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:52» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:52» input0) = SpecTec.«$free_instr:clause:52» input0 := by
  unfold «$free_instr:clause:52» SpecTec.«$free_instr:clause:52»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:53» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:53» input0) = SpecTec.«$free_instr:clause:53» input0 := by
  unfold «$free_instr:clause:53» SpecTec.«$free_instr:clause:53»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:54» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:54» input0) = SpecTec.«$free_instr:clause:54» input0 := by
  unfold «$free_instr:clause:54» SpecTec.«$free_instr:clause:54»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:55» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:55» input0) = SpecTec.«$free_instr:clause:55» input0 := by
  unfold «$free_instr:clause:55» SpecTec.«$free_instr:clause:55»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:56» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:56» input0) = SpecTec.«$free_instr:clause:56» input0 := by
  unfold «$free_instr:clause:56» SpecTec.«$free_instr:clause:56»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:57» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:57» input0) = SpecTec.«$free_instr:clause:57» input0 := by
  unfold «$free_instr:clause:57» SpecTec.«$free_instr:clause:57»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:58» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:58» input0) = SpecTec.«$free_instr:clause:58» input0 := by
  unfold «$free_instr:clause:58» SpecTec.«$free_instr:clause:58»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:59» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:59» input0) = SpecTec.«$free_instr:clause:59» input0 := by
  unfold «$free_instr:clause:59» SpecTec.«$free_instr:clause:59»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:60» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:60» input0) = SpecTec.«$free_instr:clause:60» input0 := by
  unfold «$free_instr:clause:60» SpecTec.«$free_instr:clause:60»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:61» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:61» input0) = SpecTec.«$free_instr:clause:61» input0 := by
  unfold «$free_instr:clause:61» SpecTec.«$free_instr:clause:61»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:62» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:62» input0) = SpecTec.«$free_instr:clause:62» input0 := by
  unfold «$free_instr:clause:62» SpecTec.«$free_instr:clause:62»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:63» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:63» input0) = SpecTec.«$free_instr:clause:63» input0 := by
  unfold «$free_instr:clause:63» SpecTec.«$free_instr:clause:63»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:64» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:64» input0) = SpecTec.«$free_instr:clause:64» input0 := by
  unfold «$free_instr:clause:64» SpecTec.«$free_instr:clause:64»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:65» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:65» input0) = SpecTec.«$free_instr:clause:65» input0 := by
  unfold «$free_instr:clause:65» SpecTec.«$free_instr:clause:65»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:66» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:66» input0) = SpecTec.«$free_instr:clause:66» input0 := by
  unfold «$free_instr:clause:66» SpecTec.«$free_instr:clause:66»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:67» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:67» input0) = SpecTec.«$free_instr:clause:67» input0 := by
  unfold «$free_instr:clause:67» SpecTec.«$free_instr:clause:67»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:68» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:68» input0) = SpecTec.«$free_instr:clause:68» input0 := by
  unfold «$free_instr:clause:68» SpecTec.«$free_instr:clause:68»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:69» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:69» input0) = SpecTec.«$free_instr:clause:69» input0 := by
  unfold «$free_instr:clause:69» SpecTec.«$free_instr:clause:69»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:70» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:70» input0) = SpecTec.«$free_instr:clause:70» input0 := by
  unfold «$free_instr:clause:70» SpecTec.«$free_instr:clause:70»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:71» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:71» input0) = SpecTec.«$free_instr:clause:71» input0 := by
  unfold «$free_instr:clause:71» SpecTec.«$free_instr:clause:71»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:72» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:72» input0) = SpecTec.«$free_instr:clause:72» input0 := by
  unfold «$free_instr:clause:72» SpecTec.«$free_instr:clause:72»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:73» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:73» input0) = SpecTec.«$free_instr:clause:73» input0 := by
  unfold «$free_instr:clause:73» SpecTec.«$free_instr:clause:73»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:74» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:74» input0) = SpecTec.«$free_instr:clause:74» input0 := by
  unfold «$free_instr:clause:74» SpecTec.«$free_instr:clause:74»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:75» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:75» input0) = SpecTec.«$free_instr:clause:75» input0 := by
  unfold «$free_instr:clause:75» SpecTec.«$free_instr:clause:75»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:76» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:76» input0) = SpecTec.«$free_instr:clause:76» input0 := by
  unfold «$free_instr:clause:76» SpecTec.«$free_instr:clause:76»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:77» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:77» input0) = SpecTec.«$free_instr:clause:77» input0 := by
  unfold «$free_instr:clause:77» SpecTec.«$free_instr:clause:77»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:78» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:78» input0) = SpecTec.«$free_instr:clause:78» input0 := by
  unfold «$free_instr:clause:78» SpecTec.«$free_instr:clause:78»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:79» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:79» input0) = SpecTec.«$free_instr:clause:79» input0 := by
  unfold «$free_instr:clause:79» SpecTec.«$free_instr:clause:79»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_instr:clause:80» (input0 : SpecTec.instr) :
    erase («$free_instr:clause:80» input0) = SpecTec.«$free_instr:clause:80» input0 := by
  unfold «$free_instr:clause:80» SpecTec.«$free_instr:clause:80»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_block:clause:0» (input0 : (_root_.List instr)) :
    erase («$free_block:clause:0» input0) = SpecTec.«$free_block:clause:0» input0 := by
  unfold «$free_block:clause:0» SpecTec.«$free_block:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0» (input0 : (_root_.List instr)) :
    erase («$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0» input0) = SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0» input0 := by
  unfold «$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0» SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1» (input0 : (_root_.List instr)) :
    erase («$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1» input0) = SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1» input0 := by
  unfold «$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1» SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_const:clause:0» (input0 : const) :
    erase («$free_const:clause:0» input0) = SpecTec.«$free_const:clause:0» input0 := by
  unfold «$free_const:clause:0» SpecTec.«$free_const:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_global:clause:0» (input0 : SpecTec.global) :
    erase («$free_global:clause:0» input0) = SpecTec.«$free_global:clause:0» input0 := by
  unfold «$free_global:clause:0» SpecTec.«$free_global:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_tabletype:clause:0» (input0 : tabletype) :
    erase («$free_tabletype:clause:0» input0) = SpecTec.«$free_tabletype:clause:0» input0 := by
  unfold «$free_tabletype:clause:0» SpecTec.«$free_tabletype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_table:clause:0» (input0 : SpecTec.table) :
    erase («$free_table:clause:0» input0) = SpecTec.«$free_table:clause:0» input0 := by
  unfold «$free_table:clause:0» SpecTec.«$free_table:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_elemmode:clause:0» (input0 : ((set tableidx) → (Call free))) (input1 : SpecTec.elemmode) :
    erase («$free_elemmode:clause:0» input0 input1) = SpecTec.«$free_elemmode:clause:0» (fun v0 => toOriginal (input0 v0)) input1 := by
  unfold «$free_elemmode:clause:0» SpecTec.«$free_elemmode:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_elemmode:clause:1» (input0 : ((set tableidx) → (Call free))) (input1 : SpecTec.elemmode) :
    erase («$free_elemmode:clause:1» input0 input1) = SpecTec.«$free_elemmode:clause:1» (fun v0 => toOriginal (input0 v0)) input1 := by
  unfold «$free_elemmode:clause:1» SpecTec.«$free_elemmode:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_elem:clause:0» (input0 : SpecTec.elem) :
    erase («$free_elem:clause:0» input0) = SpecTec.«$free_elem:clause:0» input0 := by
  unfold «$free_elem:clause:0» SpecTec.«$free_elem:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_datamode:clause:0» (input0 : ((set memidx) → (Call free))) (input1 : SpecTec.datamode) :
    erase («$free_datamode:clause:0» input0 input1) = SpecTec.«$free_datamode:clause:0» (fun v0 => toOriginal (input0 v0)) input1 := by
  unfold «$free_datamode:clause:0» SpecTec.«$free_datamode:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_datamode:clause:1» (input0 : ((set memidx) → (Call free))) (input1 : SpecTec.datamode) :
    erase («$free_datamode:clause:1» input0 input1) = SpecTec.«$free_datamode:clause:1» (fun v0 => toOriginal (input0 v0)) input1 := by
  unfold «$free_datamode:clause:1» SpecTec.«$free_datamode:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_data:clause:0» (input0 : SpecTec.data) :
    erase («$free_data:clause:0» input0) = SpecTec.«$free_data:clause:0» input0 := by
  unfold «$free_data:clause:0» SpecTec.«$free_data:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_importdesc:clause:0» (input0 : SpecTec.importdesc) :
    erase («$free_importdesc:clause:0» input0) = SpecTec.«$free_importdesc:clause:0» input0 := by
  unfold «$free_importdesc:clause:0» SpecTec.«$free_importdesc:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_importdesc:clause:1» (input0 : SpecTec.importdesc) :
    erase («$free_importdesc:clause:1» input0) = SpecTec.«$free_importdesc:clause:1» input0 := by
  unfold «$free_importdesc:clause:1» SpecTec.«$free_importdesc:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_importdesc:clause:2» (input0 : SpecTec.importdesc) :
    erase («$free_importdesc:clause:2» input0) = SpecTec.«$free_importdesc:clause:2» input0 := by
  unfold «$free_importdesc:clause:2» SpecTec.«$free_importdesc:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_importdesc:clause:3» (input0 : SpecTec.importdesc) :
    erase («$free_importdesc:clause:3» input0) = SpecTec.«$free_importdesc:clause:3» input0 := by
  unfold «$free_importdesc:clause:3» SpecTec.«$free_importdesc:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_importdesc:clause:4» (input0 : SpecTec.importdesc) :
    erase («$free_importdesc:clause:4» input0) = SpecTec.«$free_importdesc:clause:4» input0 := by
  unfold «$free_importdesc:clause:4» SpecTec.«$free_importdesc:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_import:clause:0» (input0 : SpecTec.«import») :
    erase («$free_import:clause:0» input0) = SpecTec.«$free_import:clause:0» input0 := by
  unfold «$free_import:clause:0» SpecTec.«$free_import:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$free_module:clause:0» (input0 : SpecTec.module) :
    erase («$free_module:clause:0» input0) = SpecTec.«$free_module:clause:0» input0 := by
  unfold «$free_module:clause:0» SpecTec.«$free_module:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_deftype:clause:0» (input0 : (_root_.List deftype)) (input1 : deftype) (input2 : deftype) :
    erase («$match_deftype:clause:0» input0 input1 input2) = SpecTec.«$match_deftype:clause:0» input0 input1 input2 := by
  unfold «$match_deftype:clause:0» SpecTec.«$match_deftype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_deftype:clause:1» (input0 : (_root_.List deftype)) (input1 : deftype) (input2 : deftype) :
    erase («$match_deftype:clause:1» input0 input1 input2) = SpecTec.«$match_deftype:clause:1» input0 input1 input2 := by
  unfold «$match_deftype:clause:1» SpecTec.«$match_deftype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_deftype:clause:2» (input0 : (_root_.List deftype)) (input1 : deftype) (input2 : deftype) :
    erase («$match_deftype:clause:2» input0 input1 input2) = SpecTec.«$match_deftype:clause:2» input0 input1 input2 := by
  unfold «$match_deftype:clause:2» SpecTec.«$match_deftype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:0» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:0» input0 input1 input2) = SpecTec.«$match_heaptype:clause:0» input0 input1 input2 := by
  unfold «$match_heaptype:clause:0» SpecTec.«$match_heaptype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:1» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:1» input0 input1 input2) = SpecTec.«$match_heaptype:clause:1» input0 input1 input2 := by
  unfold «$match_heaptype:clause:1» SpecTec.«$match_heaptype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:2» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:2» input0 input1 input2) = SpecTec.«$match_heaptype:clause:2» input0 input1 input2 := by
  unfold «$match_heaptype:clause:2» SpecTec.«$match_heaptype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:3» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:3» input0 input1 input2) = SpecTec.«$match_heaptype:clause:3» input0 input1 input2 := by
  unfold «$match_heaptype:clause:3» SpecTec.«$match_heaptype:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:4» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:4» input0 input1 input2) = SpecTec.«$match_heaptype:clause:4» input0 input1 input2 := by
  unfold «$match_heaptype:clause:4» SpecTec.«$match_heaptype:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:5» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:5» input0 input1 input2) = SpecTec.«$match_heaptype:clause:5» input0 input1 input2 := by
  unfold «$match_heaptype:clause:5» SpecTec.«$match_heaptype:clause:5»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:6» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:6» input0 input1 input2) = SpecTec.«$match_heaptype:clause:6» input0 input1 input2 := by
  unfold «$match_heaptype:clause:6» SpecTec.«$match_heaptype:clause:6»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:7» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:7» input0 input1 input2) = SpecTec.«$match_heaptype:clause:7» input0 input1 input2 := by
  unfold «$match_heaptype:clause:7» SpecTec.«$match_heaptype:clause:7»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:8» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:8» input0 input1 input2) = SpecTec.«$match_heaptype:clause:8» input0 input1 input2 := by
  unfold «$match_heaptype:clause:8» SpecTec.«$match_heaptype:clause:8»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:9» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:9» input0 input1 input2) = SpecTec.«$match_heaptype:clause:9» input0 input1 input2 := by
  unfold «$match_heaptype:clause:9» SpecTec.«$match_heaptype:clause:9»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:10» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:10» input0 input1 input2) = SpecTec.«$match_heaptype:clause:10» input0 input1 input2 := by
  unfold «$match_heaptype:clause:10» SpecTec.«$match_heaptype:clause:10»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:11» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:11» input0 input1 input2) = SpecTec.«$match_heaptype:clause:11» input0 input1 input2 := by
  unfold «$match_heaptype:clause:11» SpecTec.«$match_heaptype:clause:11»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:12» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:12» input0 input1 input2) = SpecTec.«$match_heaptype:clause:12» input0 input1 input2 := by
  unfold «$match_heaptype:clause:12» SpecTec.«$match_heaptype:clause:12»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype:clause:13» (input0 : (_root_.List deftype)) (input1 : heaptype) (input2 : heaptype) :
    erase («$match_heaptype:clause:13» input0 input1 input2) = SpecTec.«$match_heaptype:clause:13» input0 input1 input2 := by
  unfold «$match_heaptype:clause:13» SpecTec.«$match_heaptype:clause:13»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype_exists:clause:0» (input0 : (_root_.List deftype)) (input1 : (_root_.List heaptype)) (input2 : deftype) :
    erase («$match_heaptype_exists:clause:0» input0 input1 input2) = SpecTec.«$match_heaptype_exists:clause:0» input0 input1 input2 := by
  unfold «$match_heaptype_exists:clause:0» SpecTec.«$match_heaptype_exists:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype_exists:clause:1» (input0 : (_root_.List deftype)) (input1 : (_root_.List heaptype)) (input2 : deftype) :
    erase («$match_heaptype_exists:clause:1» input0 input1 input2) = SpecTec.«$match_heaptype_exists:clause:1» input0 input1 input2 := by
  unfold «$match_heaptype_exists:clause:1» SpecTec.«$match_heaptype_exists:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_heaptype_exists:clause:2» (input0 : (_root_.List deftype)) (input1 : (_root_.List heaptype)) (input2 : deftype) :
    erase («$match_heaptype_exists:clause:2» input0 input1 input2) = SpecTec.«$match_heaptype_exists:clause:2» input0 input1 input2 := by
  unfold «$match_heaptype_exists:clause:2» SpecTec.«$match_heaptype_exists:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_reftype:clause:0» (input0 : (_root_.List deftype)) (input1 : reftype) (input2 : reftype) :
    erase («$match_reftype:clause:0» input0 input1 input2) = SpecTec.«$match_reftype:clause:0» input0 input1 input2 := by
  unfold «$match_reftype:clause:0» SpecTec.«$match_reftype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_reftype:clause:1» (input0 : (_root_.List deftype)) (input1 : reftype) (input2 : reftype) :
    erase («$match_reftype:clause:1» input0 input1 input2) = SpecTec.«$match_reftype:clause:1» input0 input1 input2 := by
  unfold «$match_reftype:clause:1» SpecTec.«$match_reftype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_valtype:clause:0» (input0 : (_root_.List deftype)) (input1 : SpecTec.valtype) (input2 : SpecTec.valtype) :
    erase («$match_valtype:clause:0» input0 input1 input2) = SpecTec.«$match_valtype:clause:0» input0 input1 input2 := by
  unfold «$match_valtype:clause:0» SpecTec.«$match_valtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_valtype:clause:1» (input0 : (_root_.List deftype)) (input1 : SpecTec.valtype) (input2 : SpecTec.valtype) :
    erase («$match_valtype:clause:1» input0 input1 input2) = SpecTec.«$match_valtype:clause:1» input0 input1 input2 := by
  unfold «$match_valtype:clause:1» SpecTec.«$match_valtype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_valtype:clause:2» (input0 : (_root_.List deftype)) (input1 : SpecTec.valtype) (input2 : SpecTec.valtype) :
    erase («$match_valtype:clause:2» input0 input1 input2) = SpecTec.«$match_valtype:clause:2» input0 input1 input2 := by
  unfold «$match_valtype:clause:2» SpecTec.«$match_valtype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_valtype:clause:3» (input0 : (_root_.List deftype)) (input1 : SpecTec.valtype) (input2 : SpecTec.valtype) :
    erase («$match_valtype:clause:3» input0 input1 input2) = SpecTec.«$match_valtype:clause:3» input0 input1 input2 := by
  unfold «$match_valtype:clause:3» SpecTec.«$match_valtype:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_valtype:clause:4» (input0 : (_root_.List deftype)) (input1 : valtype) (input2 : valtype) :
    erase («$match_valtype:clause:4» input0 input1 input2) = SpecTec.«$match_valtype:clause:4» input0 input1 input2 := by
  unfold «$match_valtype:clause:4» SpecTec.«$match_valtype:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_storagetype:clause:0» (input0 : (_root_.List deftype)) (input1 : storagetype) (input2 : storagetype) :
    erase («$match_storagetype:clause:0» input0 input1 input2) = SpecTec.«$match_storagetype:clause:0» input0 input1 input2 := by
  unfold «$match_storagetype:clause:0» SpecTec.«$match_storagetype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_storagetype:clause:1» (input0 : (_root_.List deftype)) (input1 : storagetype) (input2 : storagetype) :
    erase («$match_storagetype:clause:1» input0 input1 input2) = SpecTec.«$match_storagetype:clause:1» input0 input1 input2 := by
  unfold «$match_storagetype:clause:1» SpecTec.«$match_storagetype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_storagetype:clause:2» (input0 : (_root_.List deftype)) (input1 : storagetype) (input2 : storagetype) :
    erase («$match_storagetype:clause:2» input0 input1 input2) = SpecTec.«$match_storagetype:clause:2» input0 input1 input2 := by
  unfold «$match_storagetype:clause:2» SpecTec.«$match_storagetype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_fieldtype:clause:0» (input0 : (_root_.List deftype)) (input1 : fieldtype) (input2 : fieldtype) :
    erase («$match_fieldtype:clause:0» input0 input1 input2) = SpecTec.«$match_fieldtype:clause:0» input0 input1 input2 := by
  unfold «$match_fieldtype:clause:0» SpecTec.«$match_fieldtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_fieldtype:clause:1» (input0 : (_root_.List deftype)) (input1 : fieldtype) (input2 : fieldtype) :
    erase («$match_fieldtype:clause:1» input0 input1 input2) = SpecTec.«$match_fieldtype:clause:1» input0 input1 input2 := by
  unfold «$match_fieldtype:clause:1» SpecTec.«$match_fieldtype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_fieldtype:clause:2» (input0 : (_root_.List deftype)) (input1 : fieldtype) (input2 : fieldtype) :
    erase («$match_fieldtype:clause:2» input0 input1 input2) = SpecTec.«$match_fieldtype:clause:2» input0 input1 input2 := by
  unfold «$match_fieldtype:clause:2» SpecTec.«$match_fieldtype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_arraytype:clause:0» (input0 : (_root_.List deftype)) (input1 : arraytype) (input2 : arraytype) :
    erase («$match_arraytype:clause:0» input0 input1 input2) = SpecTec.«$match_arraytype:clause:0» input0 input1 input2 := by
  unfold «$match_arraytype:clause:0» SpecTec.«$match_arraytype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_structtype:case_1:iter:0:clause:0» (input0 : (_root_.List deftype)) (input1 : (_root_.List fieldtype)) (input2 : (_root_.List fieldtype)) :
    erase («$match_structtype:case_1:iter:0:clause:0» input0 input1 input2) = SpecTec.«$match_structtype:case_1:iter:0:clause:0» input0 input1 input2 := by
  unfold «$match_structtype:case_1:iter:0:clause:0» SpecTec.«$match_structtype:case_1:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_structtype:case_1:iter:0:clause:1» (input0 : (_root_.List deftype)) (input1 : (_root_.List fieldtype)) (input2 : (_root_.List fieldtype)) :
    erase («$match_structtype:case_1:iter:0:clause:1» input0 input1 input2) = SpecTec.«$match_structtype:case_1:iter:0:clause:1» input0 input1 input2 := by
  unfold «$match_structtype:case_1:iter:0:clause:1» SpecTec.«$match_structtype:case_1:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_structtype:clause:0» (input0 : (_root_.List deftype)) (input1 : structtype) (input2 : structtype) :
    erase («$match_structtype:clause:0» input0 input1 input2) = SpecTec.«$match_structtype:clause:0» input0 input1 input2 := by
  unfold «$match_structtype:clause:0» SpecTec.«$match_structtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_structtype:clause:1» (input0 : (_root_.List deftype)) (input1 : structtype) (input2 : structtype) :
    erase («$match_structtype:clause:1» input0 input1 input2) = SpecTec.«$match_structtype:clause:1» input0 input1 input2 := by
  unfold «$match_structtype:clause:1» SpecTec.«$match_structtype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_resulttype:case_1:iter:0:clause:0» (input0 : (_root_.List deftype)) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) :
    erase («$match_resulttype:case_1:iter:0:clause:0» input0 input1 input2) = SpecTec.«$match_resulttype:case_1:iter:0:clause:0» input0 input1 input2 := by
  unfold «$match_resulttype:case_1:iter:0:clause:0» SpecTec.«$match_resulttype:case_1:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_resulttype:case_1:iter:0:clause:1» (input0 : (_root_.List deftype)) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) :
    erase («$match_resulttype:case_1:iter:0:clause:1» input0 input1 input2) = SpecTec.«$match_resulttype:case_1:iter:0:clause:1» input0 input1 input2 := by
  unfold «$match_resulttype:case_1:iter:0:clause:1» SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_resulttype:clause:0» (input0 : (_root_.List deftype)) (input1 : resulttype) (input2 : resulttype) :
    erase («$match_resulttype:clause:0» input0 input1 input2) = SpecTec.«$match_resulttype:clause:0» input0 input1 input2 := by
  unfold «$match_resulttype:clause:0» SpecTec.«$match_resulttype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_resulttype:clause:1» (input0 : (_root_.List deftype)) (input1 : resulttype) (input2 : resulttype) :
    erase («$match_resulttype:clause:1» input0 input1 input2) = SpecTec.«$match_resulttype:clause:1» input0 input1 input2 := by
  unfold «$match_resulttype:clause:1» SpecTec.«$match_resulttype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_functype:clause:0» (input0 : (_root_.List deftype)) (input1 : functype) (input2 : functype) :
    erase («$match_functype:clause:0» input0 input1 input2) = SpecTec.«$match_functype:clause:0» input0 input1 input2 := by
  unfold «$match_functype:clause:0» SpecTec.«$match_functype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_strtype:clause:0» (input0 : (_root_.List deftype)) (input1 : strtype) (input2 : strtype) :
    erase («$match_strtype:clause:0» input0 input1 input2) = SpecTec.«$match_strtype:clause:0» input0 input1 input2 := by
  unfold «$match_strtype:clause:0» SpecTec.«$match_strtype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_strtype:clause:1» (input0 : (_root_.List deftype)) (input1 : strtype) (input2 : strtype) :
    erase («$match_strtype:clause:1» input0 input1 input2) = SpecTec.«$match_strtype:clause:1» input0 input1 input2 := by
  unfold «$match_strtype:clause:1» SpecTec.«$match_strtype:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_strtype:clause:2» (input0 : (_root_.List deftype)) (input1 : strtype) (input2 : strtype) :
    erase («$match_strtype:clause:2» input0 input1 input2) = SpecTec.«$match_strtype:clause:2» input0 input1 input2 := by
  unfold «$match_strtype:clause:2» SpecTec.«$match_strtype:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$match_strtype:clause:3» (input0 : (_root_.List deftype)) (input1 : strtype) (input2 : strtype) :
    erase («$match_strtype:clause:3» input0 input1 input2) = SpecTec.«$match_strtype:clause:3» input0 input1 input2 := by
  unfold «$match_strtype:clause:3» SpecTec.«$match_strtype:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$top_of_str_type:clause:0» (input0 : (_root_.List deftype)) (input1 : strtype) :
    erase («$top_of_str_type:clause:0» input0 input1) = SpecTec.«$top_of_str_type:clause:0» input0 input1 := by
  unfold «$top_of_str_type:clause:0» SpecTec.«$top_of_str_type:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$top_of_heap_type:clause:0» (input0 : (_root_.List deftype)) (input1 : heaptype) :
    erase («$top_of_heap_type:clause:0» input0 input1) = SpecTec.«$top_of_heap_type:clause:0» input0 input1 := by
  unfold «$top_of_heap_type:clause:0» SpecTec.«$top_of_heap_type:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$top_of_heap_type:clause:1» (input0 : (_root_.List deftype)) (input1 : heaptype) :
    erase («$top_of_heap_type:clause:1» input0 input1) = SpecTec.«$top_of_heap_type:clause:1» input0 input1 := by
  unfold «$top_of_heap_type:clause:1» SpecTec.«$top_of_heap_type:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$top_of_heap_type:clause:2» (input0 : (_root_.List deftype)) (input1 : heaptype) :
    erase («$top_of_heap_type:clause:2» input0 input1) = SpecTec.«$top_of_heap_type:clause:2» input0 input1 := by
  unfold «$top_of_heap_type:clause:2» SpecTec.«$top_of_heap_type:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$top_of_heap_type:clause:3» (input0 : (_root_.List deftype)) (input1 : heaptype) :
    erase («$top_of_heap_type:clause:3» input0 input1) = SpecTec.«$top_of_heap_type:clause:3» input0 input1 := by
  unfold «$top_of_heap_type:clause:3» SpecTec.«$top_of_heap_type:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$top_of_heap_type:clause:4» (input0 : (_root_.List deftype)) (input1 : heaptype) :
    erase («$top_of_heap_type:clause:4» input0 input1) = SpecTec.«$top_of_heap_type:clause:4» input0 input1 := by
  unfold «$top_of_heap_type:clause:4» SpecTec.«$top_of_heap_type:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$top_of_heap_type:clause:5» (input0 : (_root_.List deftype)) (input1 : heaptype) :
    erase («$top_of_heap_type:clause:5» input0 input1) = SpecTec.«$top_of_heap_type:clause:5» input0 input1 := by
  unfold «$top_of_heap_type:clause:5» SpecTec.«$top_of_heap_type:clause:5»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Match_resulttype:rule:iter:0:clause:0» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) :
    erase («Match_resulttype:rule:iter:0:clause:0» input0 input1 input2) = SpecTec.«Match_resulttype:rule:iter:0:clause:0» input0 input1 input2 := by
  unfold «Match_resulttype:rule:iter:0:clause:0» SpecTec.«Match_resulttype:rule:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Match_resulttype:rule:iter:0:clause:1» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List valtype)) :
    erase («Match_resulttype:rule:iter:0:clause:1» input0 input1 input2) = SpecTec.«Match_resulttype:rule:iter:0:clause:1» input0 input1 input2 := by
  unfold «Match_resulttype:rule:iter:0:clause:1» SpecTec.«Match_resulttype:rule:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Match_resulttype:clause:0» (input0 : context) (input1 : resulttype) (input2 : resulttype) :
    erase («Match_resulttype:clause:0» input0 input1 input2) = SpecTec.«Match_resulttype:clause:0» input0 input1 input2 := by
  unfold «Match_resulttype:clause:0» SpecTec.«Match_resulttype:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$pop:clause:0» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) :
    erase («$pop:clause:0» input0 input1 input2) = SpecTec.«$pop:clause:0» input0 input1 input2 := by
  unfold «$pop:clause:0» SpecTec.«$pop:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$pop:clause:1» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) :
    erase («$pop:clause:1» input0 input1 input2) = SpecTec.«$pop:clause:1» input0 input1 input2 := by
  unfold «$pop:clause:1» SpecTec.«$pop:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$pop:clause:2» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) :
    erase («$pop:clause:2» input0 input1 input2) = SpecTec.«$pop:clause:2» input0 input1 input2 := by
  unfold «$pop:clause:2» SpecTec.«$pop:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$pop:clause:3» (input0 : context) (input1 : (SpecTec.ellipses × resulttype)) (input2 : (SpecTec.ellipses × resulttype)) :
    erase («$pop:clause:3» input0 input1 input2) = SpecTec.«$pop:clause:3» input0 input1 input2 := by
  unfold «$pop:clause:3» SpecTec.«$pop:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Heaptype_ok:clause:0» (input0 : context) (input1 : heaptype) :
    erase («Heaptype_ok:clause:0» input0 input1) = SpecTec.«Heaptype_ok:clause:0» input0 input1 := by
  unfold «Heaptype_ok:clause:0» SpecTec.«Heaptype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Heaptype_ok:clause:1» (input0 : context) (input1 : heaptype) :
    erase («Heaptype_ok:clause:1» input0 input1) = SpecTec.«Heaptype_ok:clause:1» input0 input1 := by
  unfold «Heaptype_ok:clause:1» SpecTec.«Heaptype_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Reftype_ok:clause:0» (input0 : context) (input1 : reftype) :
    erase («Reftype_ok:clause:0» input0 input1) = SpecTec.«Reftype_ok:clause:0» input0 input1 := by
  unfold «Reftype_ok:clause:0» SpecTec.«Reftype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Valtype_ok:clause:0» (input0 : context) (input1 : SpecTec.valtype) :
    erase («Valtype_ok:clause:0» input0 input1) = SpecTec.«Valtype_ok:clause:0» input0 input1 := by
  unfold «Valtype_ok:clause:0» SpecTec.«Valtype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Valtype_ok:clause:1» (input0 : context) (input1 : SpecTec.valtype) :
    erase («Valtype_ok:clause:1» input0 input1) = SpecTec.«Valtype_ok:clause:1» input0 input1 := by
  unfold «Valtype_ok:clause:1» SpecTec.«Valtype_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Valtype_ok:clause:2» (input0 : context) (input1 : SpecTec.valtype) :
    erase («Valtype_ok:clause:2» input0 input1) = SpecTec.«Valtype_ok:clause:2» input0 input1 := by
  unfold «Valtype_ok:clause:2» SpecTec.«Valtype_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Resulttype_ok:rule:iter:0:clause:0» (input0 : context) (input1 : (_root_.List valtype)) :
    erase («Resulttype_ok:rule:iter:0:clause:0» input0 input1) = SpecTec.«Resulttype_ok:rule:iter:0:clause:0» input0 input1 := by
  unfold «Resulttype_ok:rule:iter:0:clause:0» SpecTec.«Resulttype_ok:rule:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Resulttype_ok:rule:iter:0:clause:1» (input0 : context) (input1 : (_root_.List valtype)) :
    erase («Resulttype_ok:rule:iter:0:clause:1» input0 input1) = SpecTec.«Resulttype_ok:rule:iter:0:clause:1» input0 input1 := by
  unfold «Resulttype_ok:rule:iter:0:clause:1» SpecTec.«Resulttype_ok:rule:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Resulttype_ok:clause:0» (input0 : context) (input1 : resulttype) :
    erase («Resulttype_ok:clause:0» input0 input1) = SpecTec.«Resulttype_ok:clause:0» input0 input1 := by
  unfold «Resulttype_ok:clause:0» SpecTec.«Resulttype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Functype_ok:clause:0» (input0 : context) (input1 : functype) :
    erase («Functype_ok:clause:0» input0 input1) = SpecTec.«Functype_ok:clause:0» input0 input1 := by
  unfold «Functype_ok:clause:0» SpecTec.«Functype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Subtype_ok:rule:iter:0:clause:0» (input0 : context) (input1 : (_root_.List heaptype)) :
    erase («Subtype_ok:rule:iter:0:clause:0» input0 input1) = SpecTec.«Subtype_ok:rule:iter:0:clause:0» input0 input1 := by
  unfold «Subtype_ok:rule:iter:0:clause:0» SpecTec.«Subtype_ok:rule:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Subtype_ok:rule:iter:0:clause:1» (input0 : context) (input1 : (_root_.List heaptype)) :
    erase («Subtype_ok:rule:iter:0:clause:1» input0 input1) = SpecTec.«Subtype_ok:rule:iter:0:clause:1» input0 input1 := by
  unfold «Subtype_ok:rule:iter:0:clause:1» SpecTec.«Subtype_ok:rule:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Storagetype_ok:clause:0» (input0 : context) (input1 : storagetype) :
    erase («Storagetype_ok:clause:0» input0 input1) = SpecTec.«Storagetype_ok:clause:0» input0 input1 := by
  unfold «Storagetype_ok:clause:0» SpecTec.«Storagetype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Storagetype_ok:clause:1» (input0 : context) (input1 : storagetype) :
    erase («Storagetype_ok:clause:1» input0 input1) = SpecTec.«Storagetype_ok:clause:1» input0 input1 := by
  unfold «Storagetype_ok:clause:1» SpecTec.«Storagetype_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Fieldtype_ok:clause:0» (input0 : context) (input1 : fieldtype) :
    erase («Fieldtype_ok:clause:0» input0 input1) = SpecTec.«Fieldtype_ok:clause:0» input0 input1 := by
  unfold «Fieldtype_ok:clause:0» SpecTec.«Fieldtype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Structtype_ok:rule:iter:0:clause:0» (input0 : context) (input1 : (_root_.List fieldtype)) :
    erase («Structtype_ok:rule:iter:0:clause:0» input0 input1) = SpecTec.«Structtype_ok:rule:iter:0:clause:0» input0 input1 := by
  unfold «Structtype_ok:rule:iter:0:clause:0» SpecTec.«Structtype_ok:rule:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Structtype_ok:rule:iter:0:clause:1» (input0 : context) (input1 : (_root_.List fieldtype)) :
    erase («Structtype_ok:rule:iter:0:clause:1» input0 input1) = SpecTec.«Structtype_ok:rule:iter:0:clause:1» input0 input1 := by
  unfold «Structtype_ok:rule:iter:0:clause:1» SpecTec.«Structtype_ok:rule:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Structtype_ok:clause:0» (input0 : context) (input1 : structtype) :
    erase («Structtype_ok:clause:0» input0 input1) = SpecTec.«Structtype_ok:clause:0» input0 input1 := by
  unfold «Structtype_ok:clause:0» SpecTec.«Structtype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Arraytype_ok:clause:0» (input0 : context) (input1 : arraytype) :
    erase («Arraytype_ok:clause:0» input0 input1) = SpecTec.«Arraytype_ok:clause:0» input0 input1 := by
  unfold «Arraytype_ok:clause:0» SpecTec.«Arraytype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Strtype_ok:clause:0» (input0 : context) (input1 : strtype) :
    erase («Strtype_ok:clause:0» input0 input1) = SpecTec.«Strtype_ok:clause:0» input0 input1 := by
  unfold «Strtype_ok:clause:0» SpecTec.«Strtype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Strtype_ok:clause:1» (input0 : context) (input1 : strtype) :
    erase («Strtype_ok:clause:1» input0 input1) = SpecTec.«Strtype_ok:clause:1» input0 input1 := by
  unfold «Strtype_ok:clause:1» SpecTec.«Strtype_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Strtype_ok:clause:2» (input0 : context) (input1 : strtype) :
    erase («Strtype_ok:clause:2» input0 input1) = SpecTec.«Strtype_ok:clause:2» input0 input1 := by
  unfold «Strtype_ok:clause:2» SpecTec.«Strtype_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Subtype_ok:clause:0» (input0 : context) (input1 : SpecTec.subtype) :
    erase («Subtype_ok:clause:0» input0 input1) = SpecTec.«Subtype_ok:clause:0» input0 input1 := by
  unfold «Subtype_ok:clause:0» SpecTec.«Subtype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Subtype_sub_ok':clause:0» (input0 : context) (input1 : typeidx) (input2 : strtype) (input3 : heaptype) :
    erase («Subtype_sub_ok':clause:0» input0 input1 input2 input3) = SpecTec.«Subtype_sub_ok':clause:0» input0 input1 input2 input3 := by
  unfold «Subtype_sub_ok':clause:0» SpecTec.«Subtype_sub_ok':clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Subtype_sub_ok:rule:iter:0:clause:0» (input0 : context) (input1 : idx) (input2 : strtype) (input3 : (_root_.List heaptype)) :
    erase («Subtype_sub_ok:rule:iter:0:clause:0» input0 input1 input2 input3) = SpecTec.«Subtype_sub_ok:rule:iter:0:clause:0» input0 input1 input2 input3 := by
  unfold «Subtype_sub_ok:rule:iter:0:clause:0» SpecTec.«Subtype_sub_ok:rule:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Subtype_sub_ok:rule:iter:0:clause:1» (input0 : context) (input1 : idx) (input2 : strtype) (input3 : (_root_.List heaptype)) :
    erase («Subtype_sub_ok:rule:iter:0:clause:1» input0 input1 input2 input3) = SpecTec.«Subtype_sub_ok:rule:iter:0:clause:1» input0 input1 input2 input3 := by
  unfold «Subtype_sub_ok:rule:iter:0:clause:1» SpecTec.«Subtype_sub_ok:rule:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Subtype_sub_ok:clause:0» (input0 : context) (input1 : typeidx) (input2 : SpecTec.subtype) :
    erase («Subtype_sub_ok:clause:0» input0 input1 input2) = SpecTec.«Subtype_sub_ok:clause:0» input0 input1 input2 := by
  unfold «Subtype_sub_ok:clause:0» SpecTec.«Subtype_sub_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Rectype_ok:rule:iter:2:clause:0» (input0 : context) (input1 : (_root_.List deftype)) :
    erase («Rectype_ok:rule:iter:2:clause:0» input0 input1) = SpecTec.«Rectype_ok:rule:iter:2:clause:0» input0 input1 := by
  unfold «Rectype_ok:rule:iter:2:clause:0» SpecTec.«Rectype_ok:rule:iter:2:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Rectype_ok:rule:iter:2:clause:1» (input0 : context) (input1 : (_root_.List deftype)) :
    erase («Rectype_ok:rule:iter:2:clause:1» input0 input1) = SpecTec.«Rectype_ok:rule:iter:2:clause:1» input0 input1 := by
  unfold «Rectype_ok:rule:iter:2:clause:1» SpecTec.«Rectype_ok:rule:iter:2:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Rectype_ok:rule:iter:5:clause:0» (input0 : context) (input1 : (_root_.List subtype)) :
    erase («Rectype_ok:rule:iter:5:clause:0» input0 input1) = SpecTec.«Rectype_ok:rule:iter:5:clause:0» input0 input1 := by
  unfold «Rectype_ok:rule:iter:5:clause:0» SpecTec.«Rectype_ok:rule:iter:5:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Rectype_ok:rule:iter:5:clause:1» (input0 : context) (input1 : (_root_.List subtype)) :
    erase («Rectype_ok:rule:iter:5:clause:1» input0 input1) = SpecTec.«Rectype_ok:rule:iter:5:clause:1» input0 input1 := by
  unfold «Rectype_ok:rule:iter:5:clause:1» SpecTec.«Rectype_ok:rule:iter:5:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Rectype_ok:rule:iter:6:clause:0» (input0 : context) (input1 : idx) (input2 : (_root_.List n)) (input3 : (_root_.List subtype)) :
    erase («Rectype_ok:rule:iter:6:clause:0» input0 input1 input2 input3) = SpecTec.«Rectype_ok:rule:iter:6:clause:0» input0 input1 input2 input3 := by
  unfold «Rectype_ok:rule:iter:6:clause:0» SpecTec.«Rectype_ok:rule:iter:6:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Rectype_ok:rule:iter:6:clause:1» (input0 : context) (input1 : idx) (input2 : (_root_.List SpecTec.n)) (input3 : (_root_.List subtype)) :
    erase («Rectype_ok:rule:iter:6:clause:1» input0 input1 input2 input3) = SpecTec.«Rectype_ok:rule:iter:6:clause:1» input0 input1 input2 input3 := by
  unfold «Rectype_ok:rule:iter:6:clause:1» SpecTec.«Rectype_ok:rule:iter:6:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Rectype_ok:clause:0» (input0 : context) (input1 : SpecTec.rectype) :
    erase («Rectype_ok:clause:0» input0 input1) = SpecTec.«Rectype_ok:clause:0» input0 input1 := by
  unfold «Rectype_ok:clause:0» SpecTec.«Rectype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Globaltype_ok:clause:0» (input0 : context) (input1 : globaltype) :
    erase («Globaltype_ok:clause:0» input0 input1) = SpecTec.«Globaltype_ok:clause:0» input0 input1 := by
  unfold «Globaltype_ok:clause:0» SpecTec.«Globaltype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Tagtype_ok:clause:0» (input0 : context) (input1 : tagtype) :
    erase («Tagtype_ok:clause:0» input0 input1) = SpecTec.«Tagtype_ok:clause:0» input0 input1 := by
  unfold «Tagtype_ok:clause:0» SpecTec.«Tagtype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Tabletype_ok:clause:0» (input0 : context) (input1 : tabletype) :
    erase («Tabletype_ok:clause:0» input0 input1) = SpecTec.«Tabletype_ok:clause:0» input0 input1 := by
  unfold «Tabletype_ok:clause:0» SpecTec.«Tabletype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Tabletype_ok:clause:1» (input0 : context) (input1 : tabletype) :
    erase («Tabletype_ok:clause:1» input0 input1) = SpecTec.«Tabletype_ok:clause:1» input0 input1 := by
  unfold «Tabletype_ok:clause:1» SpecTec.«Tabletype_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$array_type:clause:0» (input0 : context) (input1 : typeidx) :
    erase («$array_type:clause:0» input0 input1) = SpecTec.«$array_type:clause:0» input0 input1 := by
  unfold «$array_type:clause:0» SpecTec.«$array_type:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$struct_type:clause:0» (input0 : context) (input1 : typeidx) :
    erase («$struct_type:clause:0» input0 input1) = SpecTec.«$struct_type:clause:0» input0 input1 := by
  unfold «$struct_type:clause:0» SpecTec.«$struct_type:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:$func_type:clause:0» (input0 : context) (input1 : typeidx) :
    erase («$func_type:clause:0» input0 input1) = SpecTec.«$func_type:clause:0» input0 input1 := by
  unfold «$func_type:clause:0» SpecTec.«$func_type:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Blocktype_ok:clause:0» (input0 : context) (input1 : SpecTec.blocktype) :
    erase («Blocktype_ok:clause:0» input0 input1) = SpecTec.«Blocktype_ok:clause:0» input0 input1 := by
  unfold «Blocktype_ok:clause:0» SpecTec.«Blocktype_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Blocktype_ok:clause:1» (input0 : context) (input1 : SpecTec.blocktype) :
    erase («Blocktype_ok:clause:1» input0 input1) = SpecTec.«Blocktype_ok:clause:1» input0 input1 := by
  unfold «Blocktype_ok:clause:1» SpecTec.«Blocktype_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Blocktype_ok:clause:2» (input0 : context) (input1 : SpecTec.blocktype) :
    erase («Blocktype_ok:clause:2» input0 input1) = SpecTec.«Blocktype_ok:clause:2» input0 input1 := by
  unfold «Blocktype_ok:clause:2» SpecTec.«Blocktype_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Catch_ok:clause:0» (input0 : context) (input1 : resulttype) (input2 : SpecTec.«catch») :
    erase («Catch_ok:clause:0» input0 input1 input2) = SpecTec.«Catch_ok:clause:0» input0 input1 input2 := by
  unfold «Catch_ok:clause:0» SpecTec.«Catch_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Catch_ok:clause:1» (input0 : context) (input1 : resulttype) (input2 : SpecTec.«catch») :
    erase («Catch_ok:clause:1» input0 input1 input2) = SpecTec.«Catch_ok:clause:1» input0 input1 input2 := by
  unfold «Catch_ok:clause:1» SpecTec.«Catch_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Catch_ok:clause:2» (input0 : context) (input1 : resulttype) (input2 : SpecTec.«catch») :
    erase («Catch_ok:clause:2» input0 input1 input2) = SpecTec.«Catch_ok:clause:2» input0 input1 input2 := by
  unfold «Catch_ok:clause:2» SpecTec.«Catch_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Catch_ok:clause:3» (input0 : context) (input1 : resulttype) (input2 : SpecTec.«catch») :
    erase («Catch_ok:clause:3» input0 input1 input2) = SpecTec.«Catch_ok:clause:3» input0 input1 input2 := by
  unfold «Catch_ok:clause:3» SpecTec.«Catch_ok:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:br_table:iter:4:clause:0» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List idx)) :
    erase («Instr_ok:br_table:iter:4:clause:0» input0 input1 input2) = SpecTec.«Instr_ok:br_table:iter:4:clause:0» input0 input1 input2 := by
  unfold «Instr_ok:br_table:iter:4:clause:0» SpecTec.«Instr_ok:br_table:iter:4:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:br_table:iter:4:clause:1» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List idx)) :
    erase («Instr_ok:br_table:iter:4:clause:1» input0 input1 input2) = SpecTec.«Instr_ok:br_table:iter:4:clause:1» input0 input1 input2 := by
  unfold «Instr_ok:br_table:iter:4:clause:1» SpecTec.«Instr_ok:br_table:iter:4:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:try_table:iter:0:clause:0» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List «catch»)) :
    erase («Instr_ok:try_table:iter:0:clause:0» input0 input1 input2) = SpecTec.«Instr_ok:try_table:iter:0:clause:0» input0 input1 input2 := by
  unfold «Instr_ok:try_table:iter:0:clause:0» SpecTec.«Instr_ok:try_table:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:try_table:iter:0:clause:1» (input0 : context) (input1 : (_root_.List valtype)) (input2 : (_root_.List SpecTec.«catch»)) :
    erase («Instr_ok:try_table:iter:0:clause:1» input0 input1 input2) = SpecTec.«Instr_ok:try_table:iter:0:clause:1» input0 input1 input2 := by
  unfold «Instr_ok:try_table:iter:0:clause:1» SpecTec.«Instr_ok:try_table:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instrs_ok:clause:0» (input0 : context) (input1 : inferresulttype) (input2 : (_root_.List instr)) :
    erase («Instrs_ok:clause:0» input0 input1 input2) = SpecTec.«Instrs_ok:clause:0» input0 input1 input2 := by
  unfold «Instrs_ok:clause:0» SpecTec.«Instrs_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instrs_ok:clause:1» (input0 : context) (input1 : inferresulttype) (input2 : (_root_.List instr)) :
    erase («Instrs_ok:clause:1» input0 input1 input2) = SpecTec.«Instrs_ok:clause:1» input0 input1 input2 := by
  unfold «Instrs_ok:clause:1» SpecTec.«Instrs_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:0» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:0» input0 input1 input2) = SpecTec.«Instr_ok:clause:0» input0 input1 input2 := by
  unfold «Instr_ok:clause:0» SpecTec.«Instr_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:1» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:1» input0 input1 input2) = SpecTec.«Instr_ok:clause:1» input0 input1 input2 := by
  unfold «Instr_ok:clause:1» SpecTec.«Instr_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:2» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:2» input0 input1 input2) = SpecTec.«Instr_ok:clause:2» input0 input1 input2 := by
  unfold «Instr_ok:clause:2» SpecTec.«Instr_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:3» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:3» input0 input1 input2) = SpecTec.«Instr_ok:clause:3» input0 input1 input2 := by
  unfold «Instr_ok:clause:3» SpecTec.«Instr_ok:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:4» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:4» input0 input1 input2) = SpecTec.«Instr_ok:clause:4» input0 input1 input2 := by
  unfold «Instr_ok:clause:4» SpecTec.«Instr_ok:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:5» (input0 : context) (input1 : inferresulttype) (input2 : instr) :
    erase («Instr_ok:clause:5» input0 input1 input2) = SpecTec.«Instr_ok:clause:5» input0 input1 input2 := by
  unfold «Instr_ok:clause:5» SpecTec.«Instr_ok:clause:5»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:6» (input0 : context) (input1 : inferresulttype) (input2 : instr) :
    erase («Instr_ok:clause:6» input0 input1 input2) = SpecTec.«Instr_ok:clause:6» input0 input1 input2 := by
  unfold «Instr_ok:clause:6» SpecTec.«Instr_ok:clause:6»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:7» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:7» input0 input1 input2) = SpecTec.«Instr_ok:clause:7» input0 input1 input2 := by
  unfold «Instr_ok:clause:7» SpecTec.«Instr_ok:clause:7»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:8» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:8» input0 input1 input2) = SpecTec.«Instr_ok:clause:8» input0 input1 input2 := by
  unfold «Instr_ok:clause:8» SpecTec.«Instr_ok:clause:8»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:9» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:9» input0 input1 input2) = SpecTec.«Instr_ok:clause:9» input0 input1 input2 := by
  unfold «Instr_ok:clause:9» SpecTec.«Instr_ok:clause:9»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:10» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:10» input0 input1 input2) = SpecTec.«Instr_ok:clause:10» input0 input1 input2 := by
  unfold «Instr_ok:clause:10» SpecTec.«Instr_ok:clause:10»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:11» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:11» input0 input1 input2) = SpecTec.«Instr_ok:clause:11» input0 input1 input2 := by
  unfold «Instr_ok:clause:11» SpecTec.«Instr_ok:clause:11»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:12» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:12» input0 input1 input2) = SpecTec.«Instr_ok:clause:12» input0 input1 input2 := by
  unfold «Instr_ok:clause:12» SpecTec.«Instr_ok:clause:12»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:13» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:13» input0 input1 input2) = SpecTec.«Instr_ok:clause:13» input0 input1 input2 := by
  unfold «Instr_ok:clause:13» SpecTec.«Instr_ok:clause:13»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:14» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:14» input0 input1 input2) = SpecTec.«Instr_ok:clause:14» input0 input1 input2 := by
  unfold «Instr_ok:clause:14» SpecTec.«Instr_ok:clause:14»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:15» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:15» input0 input1 input2) = SpecTec.«Instr_ok:clause:15» input0 input1 input2 := by
  unfold «Instr_ok:clause:15» SpecTec.«Instr_ok:clause:15»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:16» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:16» input0 input1 input2) = SpecTec.«Instr_ok:clause:16» input0 input1 input2 := by
  unfold «Instr_ok:clause:16» SpecTec.«Instr_ok:clause:16»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:17» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:17» input0 input1 input2) = SpecTec.«Instr_ok:clause:17» input0 input1 input2 := by
  unfold «Instr_ok:clause:17» SpecTec.«Instr_ok:clause:17»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:18» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:18» input0 input1 input2) = SpecTec.«Instr_ok:clause:18» input0 input1 input2 := by
  unfold «Instr_ok:clause:18» SpecTec.«Instr_ok:clause:18»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:19» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:19» input0 input1 input2) = SpecTec.«Instr_ok:clause:19» input0 input1 input2 := by
  unfold «Instr_ok:clause:19» SpecTec.«Instr_ok:clause:19»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:20» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:20» input0 input1 input2) = SpecTec.«Instr_ok:clause:20» input0 input1 input2 := by
  unfold «Instr_ok:clause:20» SpecTec.«Instr_ok:clause:20»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:21» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:21» input0 input1 input2) = SpecTec.«Instr_ok:clause:21» input0 input1 input2 := by
  unfold «Instr_ok:clause:21» SpecTec.«Instr_ok:clause:21»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:22» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:22» input0 input1 input2) = SpecTec.«Instr_ok:clause:22» input0 input1 input2 := by
  unfold «Instr_ok:clause:22» SpecTec.«Instr_ok:clause:22»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:23» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:23» input0 input1 input2) = SpecTec.«Instr_ok:clause:23» input0 input1 input2 := by
  unfold «Instr_ok:clause:23» SpecTec.«Instr_ok:clause:23»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:24» (input0 : context) (input1 : inferresulttype) (input2 : instr) :
    erase («Instr_ok:clause:24» input0 input1 input2) = SpecTec.«Instr_ok:clause:24» input0 input1 input2 := by
  unfold «Instr_ok:clause:24» SpecTec.«Instr_ok:clause:24»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:25» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:25» input0 input1 input2) = SpecTec.«Instr_ok:clause:25» input0 input1 input2 := by
  unfold «Instr_ok:clause:25» SpecTec.«Instr_ok:clause:25»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:26» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:26» input0 input1 input2) = SpecTec.«Instr_ok:clause:26» input0 input1 input2 := by
  unfold «Instr_ok:clause:26» SpecTec.«Instr_ok:clause:26»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:27» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:27» input0 input1 input2) = SpecTec.«Instr_ok:clause:27» input0 input1 input2 := by
  unfold «Instr_ok:clause:27» SpecTec.«Instr_ok:clause:27»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:28» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:28» input0 input1 input2) = SpecTec.«Instr_ok:clause:28» input0 input1 input2 := by
  unfold «Instr_ok:clause:28» SpecTec.«Instr_ok:clause:28»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:29» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:29» input0 input1 input2) = SpecTec.«Instr_ok:clause:29» input0 input1 input2 := by
  unfold «Instr_ok:clause:29» SpecTec.«Instr_ok:clause:29»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:30» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:30» input0 input1 input2) = SpecTec.«Instr_ok:clause:30» input0 input1 input2 := by
  unfold «Instr_ok:clause:30» SpecTec.«Instr_ok:clause:30»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:31» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:31» input0 input1 input2) = SpecTec.«Instr_ok:clause:31» input0 input1 input2 := by
  unfold «Instr_ok:clause:31» SpecTec.«Instr_ok:clause:31»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:32» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:32» input0 input1 input2) = SpecTec.«Instr_ok:clause:32» input0 input1 input2 := by
  unfold «Instr_ok:clause:32» SpecTec.«Instr_ok:clause:32»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:33» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:33» input0 input1 input2) = SpecTec.«Instr_ok:clause:33» input0 input1 input2 := by
  unfold «Instr_ok:clause:33» SpecTec.«Instr_ok:clause:33»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:34» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:34» input0 input1 input2) = SpecTec.«Instr_ok:clause:34» input0 input1 input2 := by
  unfold «Instr_ok:clause:34» SpecTec.«Instr_ok:clause:34»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:35» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:35» input0 input1 input2) = SpecTec.«Instr_ok:clause:35» input0 input1 input2 := by
  unfold «Instr_ok:clause:35» SpecTec.«Instr_ok:clause:35»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:36» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:36» input0 input1 input2) = SpecTec.«Instr_ok:clause:36» input0 input1 input2 := by
  unfold «Instr_ok:clause:36» SpecTec.«Instr_ok:clause:36»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:37» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:37» input0 input1 input2) = SpecTec.«Instr_ok:clause:37» input0 input1 input2 := by
  unfold «Instr_ok:clause:37» SpecTec.«Instr_ok:clause:37»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:38» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:38» input0 input1 input2) = SpecTec.«Instr_ok:clause:38» input0 input1 input2 := by
  unfold «Instr_ok:clause:38» SpecTec.«Instr_ok:clause:38»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:39» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:39» input0 input1 input2) = SpecTec.«Instr_ok:clause:39» input0 input1 input2 := by
  unfold «Instr_ok:clause:39» SpecTec.«Instr_ok:clause:39»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:40» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:40» input0 input1 input2) = SpecTec.«Instr_ok:clause:40» input0 input1 input2 := by
  unfold «Instr_ok:clause:40» SpecTec.«Instr_ok:clause:40»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:41» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:41» input0 input1 input2) = SpecTec.«Instr_ok:clause:41» input0 input1 input2 := by
  unfold «Instr_ok:clause:41» SpecTec.«Instr_ok:clause:41»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:42» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:42» input0 input1 input2) = SpecTec.«Instr_ok:clause:42» input0 input1 input2 := by
  unfold «Instr_ok:clause:42» SpecTec.«Instr_ok:clause:42»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:43» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:43» input0 input1 input2) = SpecTec.«Instr_ok:clause:43» input0 input1 input2 := by
  unfold «Instr_ok:clause:43» SpecTec.«Instr_ok:clause:43»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:44» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:44» input0 input1 input2) = SpecTec.«Instr_ok:clause:44» input0 input1 input2 := by
  unfold «Instr_ok:clause:44» SpecTec.«Instr_ok:clause:44»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:45» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:45» input0 input1 input2) = SpecTec.«Instr_ok:clause:45» input0 input1 input2 := by
  unfold «Instr_ok:clause:45» SpecTec.«Instr_ok:clause:45»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:46» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:46» input0 input1 input2) = SpecTec.«Instr_ok:clause:46» input0 input1 input2 := by
  unfold «Instr_ok:clause:46» SpecTec.«Instr_ok:clause:46»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:47» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:47» input0 input1 input2) = SpecTec.«Instr_ok:clause:47» input0 input1 input2 := by
  unfold «Instr_ok:clause:47» SpecTec.«Instr_ok:clause:47»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:48» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:48» input0 input1 input2) = SpecTec.«Instr_ok:clause:48» input0 input1 input2 := by
  unfold «Instr_ok:clause:48» SpecTec.«Instr_ok:clause:48»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:49» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:49» input0 input1 input2) = SpecTec.«Instr_ok:clause:49» input0 input1 input2 := by
  unfold «Instr_ok:clause:49» SpecTec.«Instr_ok:clause:49»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:50» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:50» input0 input1 input2) = SpecTec.«Instr_ok:clause:50» input0 input1 input2 := by
  unfold «Instr_ok:clause:50» SpecTec.«Instr_ok:clause:50»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:51» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:51» input0 input1 input2) = SpecTec.«Instr_ok:clause:51» input0 input1 input2 := by
  unfold «Instr_ok:clause:51» SpecTec.«Instr_ok:clause:51»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:52» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:52» input0 input1 input2) = SpecTec.«Instr_ok:clause:52» input0 input1 input2 := by
  unfold «Instr_ok:clause:52» SpecTec.«Instr_ok:clause:52»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:53» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:53» input0 input1 input2) = SpecTec.«Instr_ok:clause:53» input0 input1 input2 := by
  unfold «Instr_ok:clause:53» SpecTec.«Instr_ok:clause:53»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:54» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:54» input0 input1 input2) = SpecTec.«Instr_ok:clause:54» input0 input1 input2 := by
  unfold «Instr_ok:clause:54» SpecTec.«Instr_ok:clause:54»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:55» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:55» input0 input1 input2) = SpecTec.«Instr_ok:clause:55» input0 input1 input2 := by
  unfold «Instr_ok:clause:55» SpecTec.«Instr_ok:clause:55»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:56» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:56» input0 input1 input2) = SpecTec.«Instr_ok:clause:56» input0 input1 input2 := by
  unfold «Instr_ok:clause:56» SpecTec.«Instr_ok:clause:56»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:57» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:57» input0 input1 input2) = SpecTec.«Instr_ok:clause:57» input0 input1 input2 := by
  unfold «Instr_ok:clause:57» SpecTec.«Instr_ok:clause:57»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:58» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:58» input0 input1 input2) = SpecTec.«Instr_ok:clause:58» input0 input1 input2 := by
  unfold «Instr_ok:clause:58» SpecTec.«Instr_ok:clause:58»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:59» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:59» input0 input1 input2) = SpecTec.«Instr_ok:clause:59» input0 input1 input2 := by
  unfold «Instr_ok:clause:59» SpecTec.«Instr_ok:clause:59»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:60» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:60» input0 input1 input2) = SpecTec.«Instr_ok:clause:60» input0 input1 input2 := by
  unfold «Instr_ok:clause:60» SpecTec.«Instr_ok:clause:60»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:61» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:61» input0 input1 input2) = SpecTec.«Instr_ok:clause:61» input0 input1 input2 := by
  unfold «Instr_ok:clause:61» SpecTec.«Instr_ok:clause:61»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:62» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:62» input0 input1 input2) = SpecTec.«Instr_ok:clause:62» input0 input1 input2 := by
  unfold «Instr_ok:clause:62» SpecTec.«Instr_ok:clause:62»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:63» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:63» input0 input1 input2) = SpecTec.«Instr_ok:clause:63» input0 input1 input2 := by
  unfold «Instr_ok:clause:63» SpecTec.«Instr_ok:clause:63»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:64» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:64» input0 input1 input2) = SpecTec.«Instr_ok:clause:64» input0 input1 input2 := by
  unfold «Instr_ok:clause:64» SpecTec.«Instr_ok:clause:64»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:65» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:65» input0 input1 input2) = SpecTec.«Instr_ok:clause:65» input0 input1 input2 := by
  unfold «Instr_ok:clause:65» SpecTec.«Instr_ok:clause:65»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:66» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:66» input0 input1 input2) = SpecTec.«Instr_ok:clause:66» input0 input1 input2 := by
  unfold «Instr_ok:clause:66» SpecTec.«Instr_ok:clause:66»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:67» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:67» input0 input1 input2) = SpecTec.«Instr_ok:clause:67» input0 input1 input2 := by
  unfold «Instr_ok:clause:67» SpecTec.«Instr_ok:clause:67»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:68» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:68» input0 input1 input2) = SpecTec.«Instr_ok:clause:68» input0 input1 input2 := by
  unfold «Instr_ok:clause:68» SpecTec.«Instr_ok:clause:68»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:69» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:69» input0 input1 input2) = SpecTec.«Instr_ok:clause:69» input0 input1 input2 := by
  unfold «Instr_ok:clause:69» SpecTec.«Instr_ok:clause:69»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:70» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:70» input0 input1 input2) = SpecTec.«Instr_ok:clause:70» input0 input1 input2 := by
  unfold «Instr_ok:clause:70» SpecTec.«Instr_ok:clause:70»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:71» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:71» input0 input1 input2) = SpecTec.«Instr_ok:clause:71» input0 input1 input2 := by
  unfold «Instr_ok:clause:71» SpecTec.«Instr_ok:clause:71»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:72» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:72» input0 input1 input2) = SpecTec.«Instr_ok:clause:72» input0 input1 input2 := by
  unfold «Instr_ok:clause:72» SpecTec.«Instr_ok:clause:72»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:73» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:73» input0 input1 input2) = SpecTec.«Instr_ok:clause:73» input0 input1 input2 := by
  unfold «Instr_ok:clause:73» SpecTec.«Instr_ok:clause:73»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:74» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:74» input0 input1 input2) = SpecTec.«Instr_ok:clause:74» input0 input1 input2 := by
  unfold «Instr_ok:clause:74» SpecTec.«Instr_ok:clause:74»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:75» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:75» input0 input1 input2) = SpecTec.«Instr_ok:clause:75» input0 input1 input2 := by
  unfold «Instr_ok:clause:75» SpecTec.«Instr_ok:clause:75»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:76» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:76» input0 input1 input2) = SpecTec.«Instr_ok:clause:76» input0 input1 input2 := by
  unfold «Instr_ok:clause:76» SpecTec.«Instr_ok:clause:76»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:77» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:77» input0 input1 input2) = SpecTec.«Instr_ok:clause:77» input0 input1 input2 := by
  unfold «Instr_ok:clause:77» SpecTec.«Instr_ok:clause:77»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:78» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:78» input0 input1 input2) = SpecTec.«Instr_ok:clause:78» input0 input1 input2 := by
  unfold «Instr_ok:clause:78» SpecTec.«Instr_ok:clause:78»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:79» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:79» input0 input1 input2) = SpecTec.«Instr_ok:clause:79» input0 input1 input2 := by
  unfold «Instr_ok:clause:79» SpecTec.«Instr_ok:clause:79»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:80» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:80» input0 input1 input2) = SpecTec.«Instr_ok:clause:80» input0 input1 input2 := by
  unfold «Instr_ok:clause:80» SpecTec.«Instr_ok:clause:80»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:81» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:81» input0 input1 input2) = SpecTec.«Instr_ok:clause:81» input0 input1 input2 := by
  unfold «Instr_ok:clause:81» SpecTec.«Instr_ok:clause:81»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:82» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:82» input0 input1 input2) = SpecTec.«Instr_ok:clause:82» input0 input1 input2 := by
  unfold «Instr_ok:clause:82» SpecTec.«Instr_ok:clause:82»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:83» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:83» input0 input1 input2) = SpecTec.«Instr_ok:clause:83» input0 input1 input2 := by
  unfold «Instr_ok:clause:83» SpecTec.«Instr_ok:clause:83»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:84» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:84» input0 input1 input2) = SpecTec.«Instr_ok:clause:84» input0 input1 input2 := by
  unfold «Instr_ok:clause:84» SpecTec.«Instr_ok:clause:84»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:85» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:85» input0 input1 input2) = SpecTec.«Instr_ok:clause:85» input0 input1 input2 := by
  unfold «Instr_ok:clause:85» SpecTec.«Instr_ok:clause:85»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:86» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:86» input0 input1 input2) = SpecTec.«Instr_ok:clause:86» input0 input1 input2 := by
  unfold «Instr_ok:clause:86» SpecTec.«Instr_ok:clause:86»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:87» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:87» input0 input1 input2) = SpecTec.«Instr_ok:clause:87» input0 input1 input2 := by
  unfold «Instr_ok:clause:87» SpecTec.«Instr_ok:clause:87»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:88» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:88» input0 input1 input2) = SpecTec.«Instr_ok:clause:88» input0 input1 input2 := by
  unfold «Instr_ok:clause:88» SpecTec.«Instr_ok:clause:88»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:89» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:89» input0 input1 input2) = SpecTec.«Instr_ok:clause:89» input0 input1 input2 := by
  unfold «Instr_ok:clause:89» SpecTec.«Instr_ok:clause:89»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:90» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:90» input0 input1 input2) = SpecTec.«Instr_ok:clause:90» input0 input1 input2 := by
  unfold «Instr_ok:clause:90» SpecTec.«Instr_ok:clause:90»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:91» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:91» input0 input1 input2) = SpecTec.«Instr_ok:clause:91» input0 input1 input2 := by
  unfold «Instr_ok:clause:91» SpecTec.«Instr_ok:clause:91»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:92» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:92» input0 input1 input2) = SpecTec.«Instr_ok:clause:92» input0 input1 input2 := by
  unfold «Instr_ok:clause:92» SpecTec.«Instr_ok:clause:92»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:93» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:93» input0 input1 input2) = SpecTec.«Instr_ok:clause:93» input0 input1 input2 := by
  unfold «Instr_ok:clause:93» SpecTec.«Instr_ok:clause:93»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:94» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:94» input0 input1 input2) = SpecTec.«Instr_ok:clause:94» input0 input1 input2 := by
  unfold «Instr_ok:clause:94» SpecTec.«Instr_ok:clause:94»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:95» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:95» input0 input1 input2) = SpecTec.«Instr_ok:clause:95» input0 input1 input2 := by
  unfold «Instr_ok:clause:95» SpecTec.«Instr_ok:clause:95»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:96» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:96» input0 input1 input2) = SpecTec.«Instr_ok:clause:96» input0 input1 input2 := by
  unfold «Instr_ok:clause:96» SpecTec.«Instr_ok:clause:96»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:97» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:97» input0 input1 input2) = SpecTec.«Instr_ok:clause:97» input0 input1 input2 := by
  unfold «Instr_ok:clause:97» SpecTec.«Instr_ok:clause:97»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:98» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:98» input0 input1 input2) = SpecTec.«Instr_ok:clause:98» input0 input1 input2 := by
  unfold «Instr_ok:clause:98» SpecTec.«Instr_ok:clause:98»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Instr_ok:clause:99» (input0 : context) (input1 : inferresulttype) (input2 : SpecTec.instr) :
    erase («Instr_ok:clause:99» input0 input1 input2) = SpecTec.«Instr_ok:clause:99» input0 input1 input2 := by
  unfold «Instr_ok:clause:99» SpecTec.«Instr_ok:clause:99»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Block_ok:clause:0» (input0 : context) (input1 : instrtype) (input2 : const) :
    erase («Block_ok:clause:0» input0 input1 input2) = SpecTec.«Block_ok:clause:0» input0 input1 input2 := by
  unfold «Block_ok:clause:0» SpecTec.«Block_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Type_ok:clause:0» (input0 : context) (input1 : SpecTec.type) :
    erase («Type_ok:clause:0» input0 input1) = SpecTec.«Type_ok:clause:0» input0 input1 := by
  unfold «Type_ok:clause:0» SpecTec.«Type_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Types_ok:clause:0» (input0 : context) (input1 : (_root_.List type)) :
    erase («Types_ok:clause:0» input0 input1) = SpecTec.«Types_ok:clause:0» input0 input1 := by
  unfold «Types_ok:clause:0» SpecTec.«Types_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Types_ok:clause:1» (input0 : context) (input1 : (_root_.List type)) :
    erase («Types_ok:clause:1» input0 input1) = SpecTec.«Types_ok:clause:1» input0 input1 := by
  unfold «Types_ok:clause:1» SpecTec.«Types_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Import_ok:clause:0» (input0 : context) (input1 : «import») :
    erase («Import_ok:clause:0» input0 input1) = SpecTec.«Import_ok:clause:0» input0 input1 := by
  unfold «Import_ok:clause:0» SpecTec.«Import_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Import_ok:clause:1» (input0 : context) (input1 : «import») :
    erase («Import_ok:clause:1» input0 input1) = SpecTec.«Import_ok:clause:1» input0 input1 := by
  unfold «Import_ok:clause:1» SpecTec.«Import_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Import_ok:clause:2» (input0 : context) (input1 : «import») :
    erase («Import_ok:clause:2» input0 input1) = SpecTec.«Import_ok:clause:2» input0 input1 := by
  unfold «Import_ok:clause:2» SpecTec.«Import_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Import_ok:clause:3» (input0 : context) (input1 : «import») :
    erase («Import_ok:clause:3» input0 input1) = SpecTec.«Import_ok:clause:3» input0 input1 := by
  unfold «Import_ok:clause:3» SpecTec.«Import_ok:clause:3»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Import_ok:clause:4» (input0 : context) (input1 : «import») :
    erase («Import_ok:clause:4» input0 input1) = SpecTec.«Import_ok:clause:4» input0 input1 := by
  unfold «Import_ok:clause:4» SpecTec.«Import_ok:clause:4»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Imports_ok:clause:0» (input0 : context) (input1 : (_root_.List «import»)) :
    erase («Imports_ok:clause:0» input0 input1) = SpecTec.«Imports_ok:clause:0» input0 input1 := by
  unfold «Imports_ok:clause:0» SpecTec.«Imports_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Imports_ok:clause:1» (input0 : context) (input1 : (_root_.List «import»)) :
    erase («Imports_ok:clause:1» input0 input1) = SpecTec.«Imports_ok:clause:1» input0 input1 := by
  unfold «Imports_ok:clause:1» SpecTec.«Imports_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Func_ok:clause:0» (input0 : context) (input1 : func) :
    erase («Func_ok:clause:0» input0 input1) = SpecTec.«Func_ok:clause:0» input0 input1 := by
  unfold «Func_ok:clause:0» SpecTec.«Func_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Funcs_ok:clause:0» (input0 : context) (input1 : (_root_.List func)) :
    erase («Funcs_ok:clause:0» input0 input1) = SpecTec.«Funcs_ok:clause:0» input0 input1 := by
  unfold «Funcs_ok:clause:0» SpecTec.«Funcs_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Funcs_ok:clause:1» (input0 : context) (input1 : (_root_.List func)) :
    erase («Funcs_ok:clause:1» input0 input1) = SpecTec.«Funcs_ok:clause:1» input0 input1 := by
  unfold «Funcs_ok:clause:1» SpecTec.«Funcs_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Tag_ok:clause:0» (input0 : context) (input1 : tag) :
    erase («Tag_ok:clause:0» input0 input1) = SpecTec.«Tag_ok:clause:0» input0 input1 := by
  unfold «Tag_ok:clause:0» SpecTec.«Tag_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Tags_ok:clause:0» (input0 : context) (input1 : (_root_.List tag)) :
    erase («Tags_ok:clause:0» input0 input1) = SpecTec.«Tags_ok:clause:0» input0 input1 := by
  unfold «Tags_ok:clause:0» SpecTec.«Tags_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Tags_ok:clause:1» (input0 : context) (input1 : (_root_.List tag)) :
    erase («Tags_ok:clause:1» input0 input1) = SpecTec.«Tags_ok:clause:1» input0 input1 := by
  unfold «Tags_ok:clause:1» SpecTec.«Tags_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Start_ok:clause:0» (input0 : context) (input1 : (_root_.Option start)) :
    erase («Start_ok:clause:0» input0 input1) = SpecTec.«Start_ok:clause:0» input0 input1 := by
  unfold «Start_ok:clause:0» SpecTec.«Start_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Start_ok:clause:1» (input0 : context) (input1 : (_root_.Option start)) :
    erase («Start_ok:clause:1» input0 input1) = SpecTec.«Start_ok:clause:1» input0 input1 := by
  unfold «Start_ok:clause:1» SpecTec.«Start_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Const_ok:clause:0» (input0 : context) (input1 : valtype) (input2 : const) :
    erase («Const_ok:clause:0» input0 input1 input2) = SpecTec.«Const_ok:clause:0» input0 input1 input2 := by
  unfold «Const_ok:clause:0» SpecTec.«Const_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Table_ok:clause:0» (input0 : context) (input1 : table) :
    erase («Table_ok:clause:0» input0 input1) = SpecTec.«Table_ok:clause:0» input0 input1 := by
  unfold «Table_ok:clause:0» SpecTec.«Table_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Tables_ok:clause:0» (input0 : context) (input1 : (_root_.List table)) :
    erase («Tables_ok:clause:0» input0 input1) = SpecTec.«Tables_ok:clause:0» input0 input1 := by
  unfold «Tables_ok:clause:0» SpecTec.«Tables_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Tables_ok:clause:1» (input0 : context) (input1 : (_root_.List table)) :
    erase («Tables_ok:clause:1» input0 input1) = SpecTec.«Tables_ok:clause:1» input0 input1 := by
  unfold «Tables_ok:clause:1» SpecTec.«Tables_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Global_ok:clause:0» (input0 : context) (input1 : global) :
    erase («Global_ok:clause:0» input0 input1) = SpecTec.«Global_ok:clause:0» input0 input1 := by
  unfold «Global_ok:clause:0» SpecTec.«Global_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Globals_ok:clause:0» (input0 : context) (input1 : (_root_.List global)) :
    erase («Globals_ok:clause:0» input0 input1) = SpecTec.«Globals_ok:clause:0» input0 input1 := by
  unfold «Globals_ok:clause:0» SpecTec.«Globals_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Globals_ok:clause:1» (input0 : context) (input1 : (_root_.List global)) :
    erase («Globals_ok:clause:1» input0 input1) = SpecTec.«Globals_ok:clause:1» input0 input1 := by
  unfold «Globals_ok:clause:1» SpecTec.«Globals_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Elem_ok:rule:iter:0:clause:0» (input0 : context) (input1 : reftype) (input2 : (_root_.List const)) :
    erase («Elem_ok:rule:iter:0:clause:0» input0 input1 input2) = SpecTec.«Elem_ok:rule:iter:0:clause:0» input0 input1 input2 := by
  unfold «Elem_ok:rule:iter:0:clause:0» SpecTec.«Elem_ok:rule:iter:0:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Elem_ok:rule:iter:0:clause:1» (input0 : context) (input1 : reftype) (input2 : (_root_.List SpecTec.const)) :
    erase («Elem_ok:rule:iter:0:clause:1» input0 input1 input2) = SpecTec.«Elem_ok:rule:iter:0:clause:1» input0 input1 input2 := by
  unfold «Elem_ok:rule:iter:0:clause:1» SpecTec.«Elem_ok:rule:iter:0:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Elemmode_ok:clause:0» (input0 : context) (input1 : reftype) (input2 : SpecTec.elemmode) :
    erase («Elemmode_ok:clause:0» input0 input1 input2) = SpecTec.«Elemmode_ok:clause:0» input0 input1 input2 := by
  unfold «Elemmode_ok:clause:0» SpecTec.«Elemmode_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Elemmode_ok:clause:1» (input0 : context) (input1 : reftype) (input2 : SpecTec.elemmode) :
    erase («Elemmode_ok:clause:1» input0 input1 input2) = SpecTec.«Elemmode_ok:clause:1» input0 input1 input2 := by
  unfold «Elemmode_ok:clause:1» SpecTec.«Elemmode_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Elemmode_ok:clause:2» (input0 : context) (input1 : reftype) (input2 : SpecTec.elemmode) :
    erase («Elemmode_ok:clause:2» input0 input1 input2) = SpecTec.«Elemmode_ok:clause:2» input0 input1 input2 := by
  unfold «Elemmode_ok:clause:2» SpecTec.«Elemmode_ok:clause:2»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Elem_ok:clause:0» (input0 : context) (input1 : elem) :
    erase («Elem_ok:clause:0» input0 input1) = SpecTec.«Elem_ok:clause:0» input0 input1 := by
  unfold «Elem_ok:clause:0» SpecTec.«Elem_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Elems_ok:clause:0» (input0 : context) (input1 : (_root_.List elem)) :
    erase («Elems_ok:clause:0» input0 input1) = SpecTec.«Elems_ok:clause:0» input0 input1 := by
  unfold «Elems_ok:clause:0» SpecTec.«Elems_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Elems_ok:clause:1» (input0 : context) (input1 : (_root_.List elem)) :
    erase («Elems_ok:clause:1» input0 input1) = SpecTec.«Elems_ok:clause:1» input0 input1 := by
  unfold «Elems_ok:clause:1» SpecTec.«Elems_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Datamode_ok:clause:0» (input0 : context) (input1 : SpecTec.datamode) :
    erase («Datamode_ok:clause:0» input0 input1) = SpecTec.«Datamode_ok:clause:0» input0 input1 := by
  unfold «Datamode_ok:clause:0» SpecTec.«Datamode_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Datamode_ok:clause:1» (input0 : context) (input1 : SpecTec.datamode) :
    erase («Datamode_ok:clause:1» input0 input1) = SpecTec.«Datamode_ok:clause:1» input0 input1 := by
  unfold «Datamode_ok:clause:1» SpecTec.«Datamode_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Data_ok:clause:0» (input0 : context) (input1 : data) :
    erase («Data_ok:clause:0» input0 input1) = SpecTec.«Data_ok:clause:0» input0 input1 := by
  unfold «Data_ok:clause:0» SpecTec.«Data_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Datas_ok:clause:0» (input0 : context) (input1 : (_root_.List data)) :
    erase («Datas_ok:clause:0» input0 input1) = SpecTec.«Datas_ok:clause:0» input0 input1 := by
  unfold «Datas_ok:clause:0» SpecTec.«Datas_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Datas_ok:clause:1» (input0 : context) (input1 : (_root_.List data)) :
    erase («Datas_ok:clause:1» input0 input1) = SpecTec.«Datas_ok:clause:1» input0 input1 := by
  unfold «Datas_ok:clause:1» SpecTec.«Datas_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Local_ok:clause:0» (input0 : context) (input1 : «local») :
    erase («Local_ok:clause:0» input0 input1) = SpecTec.«Local_ok:clause:0» input0 input1 := by
  unfold «Local_ok:clause:0» SpecTec.«Local_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Local_ok:clause:1» (input0 : context) (input1 : «local») :
    erase («Local_ok:clause:1» input0 input1) = SpecTec.«Local_ok:clause:1» input0 input1 := by
  unfold «Local_ok:clause:1» SpecTec.«Local_ok:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Funcbody_ok:rule:iter:1:clause:0» (input0 : context) (input1 : (_root_.List «local»)) :
    erase («Funcbody_ok:rule:iter:1:clause:0» input0 input1) = SpecTec.«Funcbody_ok:rule:iter:1:clause:0» input0 input1 := by
  unfold «Funcbody_ok:rule:iter:1:clause:0» SpecTec.«Funcbody_ok:rule:iter:1:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Funcbody_ok:rule:iter:1:clause:1» (input0 : context) (input1 : (_root_.List SpecTec.«local»)) :
    erase («Funcbody_ok:rule:iter:1:clause:1» input0 input1) = SpecTec.«Funcbody_ok:rule:iter:1:clause:1» input0 input1 := by
  unfold «Funcbody_ok:rule:iter:1:clause:1» SpecTec.«Funcbody_ok:rule:iter:1:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Funcbody_ok:clause:0» (input0 : context) (input1 : func) :
    erase («Funcbody_ok:clause:0» input0 input1) = SpecTec.«Funcbody_ok:clause:0» input0 input1 := by
  unfold «Funcbody_ok:clause:0» SpecTec.«Funcbody_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Module_ok:rule:iter:2:clause:0» (input0 : context) (input1 : (_root_.List func)) :
    erase («Module_ok:rule:iter:2:clause:0» input0 input1) = SpecTec.«Module_ok:rule:iter:2:clause:0» input0 input1 := by
  unfold «Module_ok:rule:iter:2:clause:0» SpecTec.«Module_ok:rule:iter:2:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Module_ok:rule:iter:2:clause:1» (input0 : context) (input1 : (_root_.List SpecTec.func)) :
    erase («Module_ok:rule:iter:2:clause:1» input0 input1) = SpecTec.«Module_ok:rule:iter:2:clause:1» input0 input1 := by
  unfold «Module_ok:rule:iter:2:clause:1» SpecTec.«Module_ok:rule:iter:2:clause:1»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

theorem «erase:Module_ok:clause:0» (input0 : SpecTec.module) :
    erase («Module_ok:clause:0» input0) = SpecTec.«Module_ok:clause:0» input0 := by
  unfold «Module_ok:clause:0» SpecTec.«Module_ok:clause:0»
  repeat' first | rfl | (fail_if_no_progress dsimp only [erase]) | (split <;> try simp_all only []) | (funext x) | (fail_if_no_progress congr 1) | (cases_type SpecTec.deftype SpecTec.rectype SpecTec.subtype)

end properties.wasm_module_ok.PositiveRuntime
