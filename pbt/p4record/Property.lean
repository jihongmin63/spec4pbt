import pbt.p4record.View

namespace P4Property

def Premise (input : P4View.Input) : Prop := ∃ n : Nat, True ∧ Int.ofNat n = input

/-- This user property is an inequality, not equality with a reference output. -/
def Target (input : P4View.Input) (observed : P4View.Observation) : Prop := observed > input
def check (input : P4View.Input) (observed : P4View.Observation) : Bool := decide (observed > input)

theorem check_correct : ∀ input observed, Premise input →
    (check input observed = true ↔ Target input observed) := by
  intro input observed _
  exact ⟨of_decide_eq_true (p := observed > input), decide_eq_true (p := observed > input)⟩

end P4Property
