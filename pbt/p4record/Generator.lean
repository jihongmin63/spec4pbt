import pbt.p4record.Property
import pbt.CorrectGen

namespace P4Property

def naturals : Spec4Pbt.CorrectGen (fun _ : Nat => True) := by
  refine ⟨fun _ seed => seed, ?_⟩
  intro n
  constructor
  · intro _; trivial
  · intro _; exact ⟨0, n, rfl⟩

def correctGenerator : Spec4Pbt.CorrectGen Premise := Spec4Pbt.CorrectGen.map Int.ofNat naturals

end P4Property
