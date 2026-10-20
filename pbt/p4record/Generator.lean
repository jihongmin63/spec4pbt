import pbt.p4record.Property
import pbt.CorrectGen

namespace P4Property

open Gen.CorrectGen

def naturals : CorrectGen (fun _ : Nat => True) := s_arbNat

def correctGenerator : CorrectGen Premise :=
  convert (by
    funext input
    apply propext
    simp only [Premise, eq_comm])
    (s_bind naturals (fun n => s_pure (Int.ofNat n)))

end P4Property
