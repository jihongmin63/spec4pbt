import pbt.record.Property
import pbt.CorrectGen

namespace PartialProperty

open Gen.CorrectGen

def naturals : CorrectGen (fun _ : Nat => True) := s_arbNat

def correctGenerator : CorrectGen Premise :=
  convert (by
    funext input
    apply propext
    simp only [Premise, eq_comm])
    (s_bind naturals (fun n => s_pure (Int.ofNat n)))

end PartialProperty
