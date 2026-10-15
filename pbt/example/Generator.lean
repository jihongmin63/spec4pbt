import pbt.example.Goal
import pbt.example.EvenProofs

namespace Example

/-- Every natural number occurs for a suitable size and seed. -/
private def indices : Spec4Pbt.CorrectGen (fun _ : Nat => True) := by
  refine ⟨fun size seed => seed % (size + 1), ?_⟩
  intro n
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨n, n, ?_⟩
    exact mod_succ_self n

/-- The generator and its exact support proof are constructed together. -/
def correctGenerator : ExampleGoals.CorrectGen ExampleGoals.Premise :=
  Spec4Pbt.CorrectGen.convert
    (Spec4Pbt.CorrectGen.map (fun n : Nat => 2 * n) indices)
    (by
      intro input
      constructor
      · rintro ⟨n, _, h⟩
        exact (valid_iff_double input).mpr ⟨n, h.symm⟩
      · intro valid
        obtain ⟨n, h⟩ := (valid_iff_double input).mp valid
        exact ⟨n, True.intro, h.symm⟩)

/-- The executable generator is extracted from the certified construction. -/
def generate : ExampleGoals.Generator := correctGenerator.val

end Example
