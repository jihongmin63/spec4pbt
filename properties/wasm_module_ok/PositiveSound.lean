/- Property-local positive runtime refinement for the unchanged Wasm specification.
   Original source identity: s41537f07a12c318563e6aabf63ee533b7bcdb33a44bfeb071c4af4b8ddd8bf9a.
   Executable definitions and erasure proofs are separate; no compiler replacements. -/
import properties.wasm_module_ok.PositiveComplete
namespace properties.wasm_module_ok.PositiveRuntime
open SpecTecExecution
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
theorem sound
    (bodyCorrect : ∀ {α : Type} (c : Call α),
      erase (body c) = SpecTec.specTecBody ⟨_, toOriginal c⟩)
    (fuel : Nat) {α : Type} (plan : ExecutablePlan Call α) (start : Nat)
    (outcome : Outcome α) (final : Nat)
    (h : run fuel plan start = .done outcome final) :
    Eval SpecTec.specTecProgram (erase plan) start outcome.pack final := by
  induction fuel generalizing α plan start outcome final with
  | zero => cases h
  | succ fuel ih =>
    cases plan with
    | pure value => cases h; exact .pure value
    | unmatch => cases h; exact .unmatch
    | abort message => cases h; exact .abort message
    | freshId => cases h; exact .freshId
    | call request =>
      apply Eval.call
      change Eval _ (SpecTec.specTecBody ⟨_, toOriginal request⟩) _ _ _
      rw [← bodyCorrect request]
      exact ih _ _ _ _ h
    | primitive request =>
      simp [run, runEval, PrimitiveRunner.unavailable] at h
    | guard condition =>
      simp only [run, runEval] at h
      split at h
      · cases h; exact .guard_true ‹condition›
      · cases h; exact .guard_false ‹¬ condition›
    | bind plan next =>
      simp only [run, runEval] at h
      cases hr : runEval program (PrimitiveRunner.unavailable program) fuel plan start with
      | outOfFuel => simp [hr] at h
      | unsupportedPrimitive => simp [hr] at h
      | done first middle =>
        cases first with
        | success value =>
          simp only [hr] at h
          exact .bind_success (ih _ _ _ _ hr) (ih _ _ _ _ h)
        | unmatch =>
          simp only [hr] at h; cases h
          exact .bind_unmatch (ih _ _ _ _ hr)
        | abort message =>
          simp only [hr] at h; cases h
          exact .bind_abort (ih _ _ _ _ hr)
    | orElse plan next =>
      simp only [run, runEval] at h
      cases hr : runEval program (PrimitiveRunner.unavailable program) fuel plan start with
      | outOfFuel => simp [hr] at h
      | unsupportedPrimitive => simp [hr] at h
      | done first middle =>
        cases first with
        | success value =>
          simp only [hr] at h; cases h
          exact .orElse_success (ih _ _ _ _ hr)
        | unmatch =>
          simp only [hr] at h
          exact .orElse_unmatch (ih _ _ _ _ hr) (ih _ _ _ _ h)
        | abort message =>
          simp only [hr] at h; cases h
          exact .orElse_abort (ih _ _ _ _ hr)
    | notHold plan =>
      simp only [run, runEval] at h
      cases hr : runEval program (PrimitiveRunner.unavailable program) fuel plan start with
      | outOfFuel => simp [hr] at h
      | unsupportedPrimitive => simp [hr] at h
      | done first middle =>
        cases first with
        | success value =>
          simp only [hr] at h; cases h
          exact .notHold_unmatch (ih _ _ _ _ hr)
        | unmatch =>
          simp only [hr] at h; cases h
          exact .notHold_success (ih _ _ _ _ hr)
        | abort message =>
          simp only [hr] at h; cases h
          exact .notHold_abort (ih _ _ _ _ hr)

end properties.wasm_module_ok.PositiveRuntime
