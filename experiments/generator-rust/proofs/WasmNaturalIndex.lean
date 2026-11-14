import WasmNaturalWord
import WasmReplaySteps
import WasmChoiceSafety
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace RustWasm
open Aeneas Aeneas.Std generator_rust wasm.natural

/-- Every index below an arbitrary natural bound has a finite actual Rust replay.
The witness preserves arbitrary trailing tape, trace, cursor and remaining work. -/
theorem natural_index_replay (bound selected : Nat) (inRange : selected < bound) :
    ∃ cells : List U64, ∀ (rest trace : List U64) (offset work : Nat),
      wasm.choices.pick_natural (naturalLiteral bound)
        (replayState (cells ++ rest) trace offset (work + cells.length)) =
        Result.ok (.Ok (naturalLiteral selected,
          replayState rest (cells.reverse ++ trace) (offset + cells.length) work)) := by
  induction selected generalizing bound with
  | zero =>
      by_cases bounded : bound < 18446744073709551616
      · let wordBound : U64 := UScalar.ofNatCore bound bounded
        refine ⟨[0#u64], ?_⟩
        intro rest trace offset work
        have picked := pick_word_state wordBound 0#u64 rest trace offset work (by
          simp [wordBound]; omega)
        rw [wasm.choices.pick_natural, literal_to_word]
        simp [wordEncoding, bounded, wordBound, picked, natural_from_word,
          core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
      · refine ⟨[0#u64], ?_⟩
        intro rest trace offset work
        have picked := pick_word_state 2#u64 0#u64 rest trace offset work (by decide)
        rw [wasm.choices.pick_natural, literal_to_word]
        simp [wordEncoding, bounded, picked, naturalLiteral,
          core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
  | succ selected ih =>
      by_cases bounded : bound < 18446744073709551616
      · let wordBound : U64 := UScalar.ofNatCore bound bounded
        let cell : U64 := UScalar.ofNatCore (selected + 1) (by scalar_tac)
        refine ⟨[cell], ?_⟩
        intro rest trace offset work
        have picked := pick_word_state wordBound cell rest trace offset work (by
          simpa [wordBound, cell] using inRange)
        rw [wasm.choices.pick_natural, literal_to_word]
        simp [wordEncoding, bounded, wordBound, picked, natural_from_word, cell,
          core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair]
      · obtain ⟨cells, recurse⟩ := ih (bound - 1) (by omega)
        refine ⟨1#u64 :: cells, ?_⟩
        intro rest trace offset work
        have picked := pick_word_state 2#u64 1#u64 (cells ++ rest) trace offset
          (work + cells.length) (by decide)
        have previous : wasm.natural.decrement (naturalLiteral bound) =
            Result.ok (some (naturalLiteral (bound - 1))) := by
          have positiveBound : bound = (bound - 1) + 1 := by omega
          conv_lhs => rw [positiveBound]
          exact decrement_literal (bound - 1)
        rw [wasm.choices.pick_natural, literal_to_word]
        simp only [wordEncoding, dif_neg bounded, bind_ok, bind_tc_ok, List.cons_append,
          List.length_cons, Nat.add_assoc] at picked ⊢
        rw [picked]
        simp only [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, bind_ok, bind_tc_ok,
          reduceCtorEq, ↓reduceIte, copy_natural_eq, previous]
        rw [recurse]
        simp [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, increment_literal,
          List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- All successful selections, including seeded selections, lie below the input bound. -/
theorem natural_index_spec (bound : Nat) (choices : wasm.choices.Choices) :
    wasm.choices.pick_natural (naturalLiteral bound) choices ⦃ result =>
      match result with
      | .Err _ => True
      | .Ok (value, _) => naturalValue value < bound ⦄ := by
  induction bound using Nat.strong_induction_on generalizing choices with
  | h bound ih =>
      rw [wasm.choices.pick_natural, literal_to_word]
      by_cases bounded : bound < 18446744073709551616
      · simp only [wordEncoding, dif_pos bounded, bind_ok, bind_tc_ok]
        apply WP.spec_bind (pick_word_range (UScalar.ofNatCore bound bounded) choices)
        intro result range
        cases result with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, core.convert.FromSame.from]
        | Ok pair =>
            rcases pair with ⟨value, state⟩
            simp only [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, bind_ok, bind_tc_ok]
            rw [natural_from_word]
            simpa using range
      · have previous : wasm.natural.decrement (naturalLiteral bound) =
            Result.ok (some (naturalLiteral (bound - 1))) := by
          have positiveBound : bound = (bound - 1) + 1 := by omega
          conv_lhs => rw [positiveBound]
          exact decrement_literal (bound - 1)
        simp only [wordEncoding, dif_neg bounded, bind_ok, bind_tc_ok]
        apply WP.spec_bind (pick_word_range 2#u64 choices)
        intro result range
        cases result with
        | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, core.convert.FromSame.from]
        | Ok pair =>
            rcases pair with ⟨tag, state⟩
            simp only [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, bind_ok, bind_tc_ok]
            by_cases zero : tag = 0#u64
            · simp [zero, naturalValue]
              omega
            · simp only [zero, ↓reduceIte, copy_natural_eq, bind_ok, bind_tc_ok, previous]
              apply WP.spec_bind (ih (bound - 1) (by omega) state)
              intro result smaller
              cases result with
              | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame, core.convert.FromSame.from]
              | Ok pair =>
                  rcases pair with ⟨value, finalState⟩
                  obtain ⟨next, incrementRun, incrementValue⟩ := increment_total value
                  simp only [core.result.Result.Insts.CoreOpsTry.branch, ↓uncurry_apply_pair, bind_ok, bind_tc_ok,
                    incrementRun, WP.spec_ok]
                  change naturalValue value < bound - 1 at smaller
                  omega

/-- Soundness concerns every successful actual execution, not only witness tapes. -/
theorem natural_index_sound (bound value : Natural) (choices finalState : wasm.choices.Choices)
    (success : wasm.choices.pick_natural bound choices = Result.ok (.Ok (value, finalState))) :
    naturalValue value < naturalValue bound := by
  have encoded : bound = naturalLiteral (naturalValue bound) := by
    apply naturalValue_injective
    simp
  have correct := natural_index_spec (naturalValue bound) choices
  rw [← encoded, success] at correct
  simpa using correct

open Lean Elab Command in
run_cmd do
  let declarations := [
    ``positive_to_word, ``natural_to_word, ``literal_to_word, ``natural_from_word,
    ``pick_word_range, ``natural_index_replay, ``natural_index_spec, ``natural_index_sound]
  for declaration in declarations do
    let axioms ← liftCoreM (collectAxioms declaration)
    for dependency in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{declaration} depends on forbidden axiom {dependency}"
    logInfo m!"{declaration}: checked; axioms = {axioms.toList}"

end RustWasm
