import pbt.record.Property
import pbt.CorrectGen

namespace PartialProperty

def naturals : Spec4Pbt.CorrectGen (fun _ : Nat => True) := by
  refine ⟨fun _ seed => seed, ?_⟩
  intro n
  constructor
  · intro _; trivial
  · intro _; exact ⟨0, n, rfl⟩

def correctGenerator : Spec4Pbt.CorrectGen Premise := Spec4Pbt.CorrectGen.map Int.ofNat naturals

end PartialProperty
