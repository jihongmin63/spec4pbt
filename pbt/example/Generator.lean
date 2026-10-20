import pbt.example.Goal
import pbt.example.EvenProofs

namespace Example

open Gen.CorrectGen

/-- A Palamedes indexed generator followed by a manual bind and return. -/
private def doubled : CorrectGen
    (fun n : Nat => ∃ k, True ∧ n = 2 * k) :=
  s_bind s_arbNat (fun k => s_pure (2 * k))

/-- Exact support of the extracted generator is the specification premise. -/
def correctGenerator : ExampleGoals.CorrectGen ExampleGoals.Premise :=
  convert (by
    funext n
    apply propext
    constructor
    · rintro ⟨k, _, rfl⟩
      exact (valid_iff_double (2 * k)).mpr ⟨k, rfl⟩
    · intro valid
      obtain ⟨k, h⟩ := (valid_iff_double n).mp valid
      exact ⟨k, True.intro, h⟩) doubled

/-- Erase the support proof; the remaining value is Palamedes's `Gen` tree. -/
def generate : Gen ExampleGoals.Input := correctGenerator.val

theorem generate_support (n : Nat) :
    Gen.support generate n ↔ ExampleGoals.Premise n := by
  exact Iff.of_eq (congrFun correctGenerator.property n)

end Example
