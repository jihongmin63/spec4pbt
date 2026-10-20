import pbt.ae.Property
import pbt.CorrectGen

namespace AeProperty

open Gen.CorrectGen

def naturals : CorrectGen (fun _ : Nat => True) := s_arbNat

def correctGenerator : CorrectGen Premise :=
  convert (by
    funext input
    apply propext
    simp only [Premise, eq_comm])
    (s_pick (s_bind naturals (fun n => s_pure (literal n)))
      (s_pick (s_bind naturals (fun n => s_pure (addition n)))
              (s_bind naturals (fun n => s_pure (subtraction n)))))

end AeProperty
