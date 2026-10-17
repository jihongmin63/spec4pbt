@[reducible] instance testTypes : SpecTecExternTypes where
  json := Unit
  archState := Nat
  objectState := Unit
  decEqJson := inferInstance
  decEqArchState := inferInstance
  decEqObjectState := inferInstance

namespace SpecTec
open SpecTecExecution

-- Every well-typed output is admitted, including one the old model excluded.
example : «$init_archState» (7 : Nat) := .allowed (7 : Nat)
example : «$init_archState» (8 : Nat) := .allowed (8 : Nat)

-- The extern succeeds in both derivations. Its caller's guard determines
-- whether the first clause succeeds or the next clause is tried.
example : «$read_or_default» (7 : Nat) 1 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_success (.bind_success
    (.call (.primitive ⟨(7 : Nat), rfl, .allowed (7 : Nat)⟩))
    (.bind_success (.guard_true rfl) (.pure 1))))

example : «$read_or_default» (7 : Nat) 9 := by
  refine ⟨0, ?_⟩
  exact .call (.orElse_unmatch (.bind_success
    (.call (.primitive ⟨(8 : Nat), rfl, .allowed (8 : Nat)⟩))
    (.bind_unmatch (.guard_false (by decide))))
    (.orElse_success (.pure 9)))

-- An extern itself cannot provide failure or abort evidence.
example : ¬ Eval specTecProgram (.call ⟨archState, SpecTecCall.«$init_archState»⟩) 0 .unmatch 0 := by
  intro h
  cases h with
  | call h => cases h with
    | primitive h => exact h

example (message : String) :
    ¬ Eval specTecProgram (.call ⟨archState, SpecTecCall.«$init_archState»⟩) 0 (.abort message) 0 := by
  intro h
  cases h with
  | call h => cases h with
    | primitive h => exact h

section
variable [SpecTecExternTypes]
example (state : archState) : «$init_archState» state := .allowed state
end
end SpecTec
