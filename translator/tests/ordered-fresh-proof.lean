namespace SpecTec
open SpecTecExecution

syntax "prove_fresh_execution" : tactic
macro_rules
  | `(tactic| prove_fresh_execution) => `(tactic|
      first
        | exact Eval.pure _
        | exact Eval.freshId
        | exact Eval.unmatch
        | exact Eval.abort _
        | apply Eval.guard_true; decide
        | apply Eval.guard_false; decide
        | apply Eval.call; prove_fresh_execution
        | apply Eval.orElse_success; prove_fresh_execution
        | apply Eval.orElse_unmatch; prove_fresh_execution; prove_fresh_execution
        | apply Eval.orElse_abort; prove_fresh_execution
        | apply Eval.bind_success; prove_fresh_execution; prove_fresh_execution
        | apply Eval.bind_unmatch; prove_fresh_execution
        | apply Eval.bind_abort; prove_fresh_execution
        | apply Eval.notHold_success; prove_fresh_execution
        | apply Eval.notHold_unmatch; prove_fresh_execution
        | apply Eval.notHold_abort; prove_fresh_execution)

-- Internal execution composes at an arbitrary supply without public wrappers.
theorem freshOne_at (n supply : Nat) :
    Eval specTecProgram (.call ⟨typeId, SpecTecCall.FreshOne n⟩) supply
      (.success (.of (freshName supply))) (supply + 1) := by
  apply Eval.call
  apply Eval.orElse_success
  exact .bind_success (.call .freshId) (.pure _)

example : FreshOne 7 "FRESH__0" := ⟨1, freshOne_at 7 0⟩
example : «$fresh_typeId» "FRESH__0" := ⟨1, .call .freshId⟩
example : FreshPair 7 "FRESH__0" "FRESH__1" := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : FreshMismatch 7 "FRESH__0" := by
  refine ⟨1, ?_⟩; prove_fresh_execution
example : FailedCaller 7 "FRESH__0" := by
  refine ⟨1, ?_⟩; prove_fresh_execution
example : NegatedFailure 7 "FRESH__0" := by
  refine ⟨1, ?_⟩; prove_fresh_execution
example : NegatedSuccess 7 "FRESH__0" := by
  refine ⟨1, ?_⟩; prove_fresh_execution
example : «$pair» ("FRESH__0", "FRESH__1") := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : «$callback_pair» ("FRESH__0", "FRESH__1") := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : «$fresh_typeIds» 0 [] := by
  refine ⟨0, ?_⟩; prove_fresh_execution
example : «$fresh_typeIds» 3 ["FRESH__0", "FRESH__1", "FRESH__2"] := by
  refine ⟨3, ?_⟩; prove_fresh_execution
example : «$many» [4, 4, 4] ["FRESH__0", "FRESH__1", "FRESH__2"] := by
  refine ⟨3, ?_⟩; prove_fresh_execution
example : «$debug_fresh» "FRESH__1" := by
  refine ⟨2, ?_⟩; prove_fresh_execution
example : «$debug_iter» [7, 7] "FRESH__2" := by
  refine ⟨3, ?_⟩; prove_fresh_execution
example : «$debug_failure» "FRESH__0" := by
  refine ⟨1, ?_⟩; prove_fresh_execution

example : Eval specTecProgram
    (.call ⟨Int, SpecTecCall.«$fresh_then_abort»⟩) 0
    (.abort "builtin $text_to_int failed") 1 := by prove_fresh_execution
example : Eval specTecProgram
    (.call ⟨typeId, SpecTecCall.«$debug_abort»⟩) 0
    (.abort "builtin $text_to_int failed") 1 := by prove_fresh_execution

theorem freshPrimitivesDet : PrimitiveDeterministic specTecProgram := by
  intro _ _ _ h; exact False.elim h

example : ¬ FreshOne 7 "FRESH__1" := by
  rintro ⟨final, h⟩
  have eq : freshName 0 = "FRESH__1" := by
    simpa only [Outcome.success.injEq, Value.of.injEq, heq_eq_eq, true_and] using
      (eval_deterministic freshPrimitivesDet (freshOne_at 7 0) h).1
  exact (by decide : freshName 0 ≠ "FRESH__1") eq

theorem freshMismatch_exec : Eval specTecProgram
    (.call ⟨typeId, SpecTecCall.FreshMismatch 7⟩) 0
    (.success (.of "FRESH__0")) 1 := by prove_fresh_execution

example : ∃ index, Selected specTecProgram () (FreshMismatch_clauses 7)
    0 index (.of "FRESH__0") 1 :=
  (firstSuccess_success_iff _ _ _ _ _).mp (eval_call_iff.mp freshMismatch_exec)

-- No extra supply argument appears in any request or public API.
example : Nat → SpecTecCall typeId := SpecTecCall.FreshOne
example : Nat → typeId → Prop := FreshOne
example : Nonempty (Nat → Plan SpecTecRequest) := ⟨«FreshOne:clause:0»⟩
example : SpecTecCall typeId := SpecTecCall.«$fresh_typeId»

end SpecTec
