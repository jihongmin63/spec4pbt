import pbt.SpectecRuntime.Execution
/- Typed, executable refinement of SpecTecExecution. Embedded after that library. -/
set_option autoImplicit false

namespace SpecTecExecution

universe u

def Outcome.pack {α : Type} : Outcome α → Outcome Value
  | .success value => .success (.of value)
  | .unmatch => .unmatch
  | .abort message => .abort message

/-- Keeping the output index makes bind executable without dynamic casts. -/
inductive ExecutablePlan (Call : Type → Type u) : Type → Type (max u 1) where
  | pure {α : Type} (value : α) : ExecutablePlan Call α
  | unmatch {α : Type} : ExecutablePlan Call α
  | abort {α : Type} (message : String) : ExecutablePlan Call α
  | freshId : ExecutablePlan Call String
  | call {α : Type} (request : Call α) : ExecutablePlan Call α
  | primitive {α : Type} (request : Call α) : ExecutablePlan Call α
  | guard (condition : Prop) [Decidable condition] : ExecutablePlan Call Unit
  | bind {α β : Type} (plan : ExecutablePlan Call α)
      (next : α → ExecutablePlan Call β) : ExecutablePlan Call β
  | orElse {α : Type} (plan : ExecutablePlan Call α)
      (next : Unit → ExecutablePlan Call α) : ExecutablePlan Call α
  | notHold {α : Type} (plan : ExecutablePlan Call α) : ExecutablePlan Call Unit

def ExecutablePlan.erase {Call : Type → Type u} {α : Type} :
    ExecutablePlan Call α → Plan (Sigma Call)
  | .pure value => .pure value
  | .unmatch => .unmatch
  | .abort message => .abort message
  | .freshId => .freshId
  | .call request => .call ⟨_, request⟩
  | .primitive request => .primitive ⟨_, request⟩
  | @ExecutablePlan.guard _ condition _ => .guard condition
  | .bind plan next => .bind plan.erase (fun value => (next value).erase)
  | .orElse plan next => .orElse plan.erase (fun arg => (next arg).erase)
  | .notHold plan => .notHold plan.erase

def ExecutablePlan.require {Call : Type → Type u} (condition : Prop)
    [Decidable condition] (message : String) : ExecutablePlan Call Unit :=
  .orElse (.guard condition) (fun () => .abort message)

abbrev ExecutablePlan.Clause (Call : Type → Type u) (I α : Type) :=
  I → ExecutablePlan Call α

def ExecutablePlan.firstSuccess {Call : Type → Type u} {I α : Type}
    (clauses : List (ExecutablePlan.Clause Call I α)) (input : I) : ExecutablePlan Call α :=
  match clauses with
  | [] => .unmatch
  | clause :: rest => .orElse (clause input) (fun () => firstSuccess rest input)

structure ExecutableProgram (Call : Type → Type u) where
  body : {α : Type} → Call α → ExecutablePlan Call α
  primitive : Sigma Call → Outcome Value → Prop

def ExecutableProgram.erase {Call : Type → Type u} (program : ExecutableProgram Call) :
    Program (Sigma Call) where
  body request := (program.body request.2).erase
  primitive := program.primitive

/-- A partial implementation may decline a request, but every answer is certified. -/
structure PrimitiveRunner {Call : Type → Type u} (program : ExecutableProgram Call) where
  run : {α : Type} → Call α → Option (Outcome α)
  sound : ∀ {α : Type} (request : Call α) (outcome : Outcome α),
    run request = some outcome → program.primitive ⟨α, request⟩ outcome.pack

def PrimitiveRunner.unavailable {Call : Type → Type u} (program : ExecutableProgram Call) :
    PrimitiveRunner program where
  run _ := none
  sound _ _ h := by cases h

/-- Only `done` describes a semantic outcome. Neither incomplete result is unmatch. -/
inductive RunResult (α : Type) where
  | done (outcome : Outcome α) (supply : Nat)
  | outOfFuel
  | unsupportedPrimitive
  deriving DecidableEq, Repr

/-- Fuel bounds derivation height. Each recursive child receives one less fuel. -/
def runEval {Call : Type → Type u} (program : ExecutableProgram Call)
    (primitives : PrimitiveRunner program) :
    Nat → {α : Type} → ExecutablePlan Call α → Nat → RunResult α
  | 0, _, _, _ => .outOfFuel
  | fuel + 1, _, plan, supply =>
    match plan with
    | .pure value => .done (.success value) supply
    | .unmatch => .done .unmatch supply
    | .abort message => .done (.abort message) supply
    | .freshId => .done (.success (freshName supply)) (supply + 1)
    | .call request => runEval program primitives fuel (program.body request) supply
    | .primitive request => match primitives.run request with
      | some outcome => .done outcome supply
      | none => .unsupportedPrimitive
    | @ExecutablePlan.guard _ condition dec =>
      letI := dec
      if condition then .done (.success ()) supply else .done .unmatch supply
    | .bind plan next => match runEval program primitives fuel plan supply with
      | .done (.success value) middle => runEval program primitives fuel (next value) middle
      | .done .unmatch final => .done .unmatch final
      | .done (.abort message) final => .done (.abort message) final
      | .outOfFuel => .outOfFuel
      | .unsupportedPrimitive => .unsupportedPrimitive
    | .orElse plan next => match runEval program primitives fuel plan supply with
      | .done .unmatch _ => runEval program primitives fuel (next ()) supply
      | .done (.success value) final => .done (.success value) final
      | .done (.abort message) final => .done (.abort message) final
      | .outOfFuel => .outOfFuel
      | .unsupportedPrimitive => .unsupportedPrimitive
    | .notHold plan => match runEval program primitives fuel plan supply with
      | .done .unmatch final => .done (.success ()) final
      | .done (.success _) final => .done .unmatch final
      | .done (.abort message) final => .done (.abort message) final
      | .outOfFuel => .outOfFuel
      | .unsupportedPrimitive => .unsupportedPrimitive

theorem runEval_sound {Call : Type → Type u} (program : ExecutableProgram Call)
    (primitives : PrimitiveRunner program) (fuel : Nat) {α : Type}
    (plan : ExecutablePlan Call α) (start : Nat) (outcome : Outcome α) (final : Nat)
    (h : runEval program primitives fuel plan start = .done outcome final) :
    Eval program.erase plan.erase start outcome.pack final := by
  induction fuel generalizing α plan start outcome final with
  | zero => cases h
  | succ fuel ih =>
    cases plan with
    | pure value => cases h; exact .pure value
    | unmatch => cases h; exact .unmatch
    | abort message => cases h; exact .abort message
    | freshId => cases h; exact .freshId
    | call request => exact .call (ih _ _ _ _ h)
    | primitive request =>
      simp only [runEval] at h
      cases hr : primitives.run request with
      | none => simp [hr] at h
      | some value =>
        have hp := primitives.sound request value hr
        simp only [hr] at h
        cases h
        exact .primitive hp
    | guard condition =>
      simp only [runEval] at h
      split at h
      · cases h; exact .guard_true ‹condition›
      · cases h; exact .guard_false ‹¬ condition›
    | bind plan next =>
      simp only [runEval] at h
      cases hr : runEval program primitives fuel plan start with
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
      simp only [runEval] at h
      cases hr : runEval program primitives fuel plan start with
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
      simp only [runEval] at h
      cases hr : runEval program primitives fuel plan start with
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

/-- A completed computation is unchanged by increasing its fuel. -/
theorem runEval_mono {Call : Type → Type u} (program : ExecutableProgram Call)
    (primitives : PrimitiveRunner program) {fuel more : Nat} (le : fuel ≤ more)
    {α : Type} (plan : ExecutablePlan Call α) (start : Nat)
    (outcome : Outcome α) (final : Nat)
    (h : runEval program primitives fuel plan start = .done outcome final) :
    runEval program primitives more plan start = .done outcome final := by
  induction fuel generalizing more α plan start outcome final with
  | zero => cases h
  | succ fuel ih =>
    cases more with
    | zero => cases le
    | succ more =>
      have le' := Nat.le_of_succ_le_succ le
      cases plan with
      | pure value | unmatch | abort message | freshId | primitive request | guard condition =>
        exact h
      | call request => exact ih le' _ _ _ _ h
      | bind plan next =>
        simp only [runEval] at h ⊢
        cases hr : runEval program primitives fuel plan start with
        | outOfFuel => simp [hr] at h
        | unsupportedPrimitive => simp [hr] at h
        | done first middle =>
          rw [ih le' _ _ _ _ hr]
          cases first with
          | success value => exact ih le' _ _ _ _ (by simpa only [hr] using h)
          | unmatch | abort message => simpa only [hr] using h
      | orElse plan next =>
        simp only [runEval] at h ⊢
        cases hr : runEval program primitives fuel plan start with
        | outOfFuel => simp [hr] at h
        | unsupportedPrimitive => simp [hr] at h
        | done first middle =>
          rw [ih le' _ _ _ _ hr]
          cases first with
          | unmatch => exact ih le' _ _ _ _ (by simpa only [hr] using h)
          | success value | abort message => simpa only [hr] using h
      | notHold plan =>
        simp only [runEval] at h ⊢
        cases hr : runEval program primitives fuel plan start with
        | outOfFuel => simp [hr] at h
        | unsupportedPrimitive => simp [hr] at h
        | done first middle =>
          rw [ih le' _ _ _ _ hr]
          simpa only [hr] using h

end SpecTecExecution
