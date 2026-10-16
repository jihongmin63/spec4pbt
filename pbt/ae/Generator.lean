import pbt.ae.Property
import pbt.CorrectGen

namespace AeProperty

def naturals : Spec4Pbt.CorrectGen (fun _ : Nat => True) := by
  refine ⟨fun _ seed => seed, ?_⟩
  intro n
  constructor
  · intro _; trivial
  · intro _; exact ⟨0, n, rfl⟩

def correctGenerator : Spec4Pbt.CorrectGen Premise :=
  Spec4Pbt.CorrectGen.pick (Spec4Pbt.CorrectGen.map literal naturals)
    (Spec4Pbt.CorrectGen.pick (Spec4Pbt.CorrectGen.map addition naturals)
                            (Spec4Pbt.CorrectGen.map subtraction naturals))

end AeProperty
