import pbt.record.View

namespace PartialProperty

def Premise (input : PartialView.Input) : Prop := ∃ n : Nat, True ∧ Int.ofNat n = input

/-- This user property is an inequality, not equality with a reference output. -/
def Target (input : PartialView.Input) (observed : PartialView.Observation) : Prop := observed > input
def check (input : PartialView.Input) (observed : PartialView.Observation) : Bool := decide (observed > input)

theorem check_correct : ∀ input observed, Premise input →
    (check input observed = true ↔ Target input observed) := by
  intro input observed _
  exact ⟨of_decide_eq_true (p := observed > input), decide_eq_true (p := observed > input)⟩

end PartialProperty
