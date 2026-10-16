import pbt.ae.View

namespace AeProperty

def literal (n : Nat) : AeSpec.expr := .c0 (Int.ofNat n)
def addition (n : Nat) : AeSpec.expr := .c1 (literal n) (.c0 2)
def subtraction (n : Nat) : AeSpec.expr := .c2 (literal n) (.c0 2)

/-- The example samples natural literals, n + 2, and n - 2. -/
def Premise (e : AeView.Input) : Prop :=
  (∃ n : Nat, True ∧ literal n = e) ∨
  ((∃ n : Nat, True ∧ addition n = e) ∨ (∃ n : Nat, True ∧ subtraction n = e))

def eval : AeSpec.expr → Int
  | .c0 n => n
  | .c1 a b => eval a + eval b
  | .c2 a b => eval a - eval b

def Target (e : AeView.Input) (observed : AeView.Observation) : Prop := observed = eval e
def check (e : AeView.Input) (observed : AeView.Observation) : Bool := decide (observed = eval e)

theorem check_correct : ∀ e observed, Premise e → (check e observed = true ↔ Target e observed) := by
  intro e observed _
  exact ⟨of_decide_eq_true (p := observed = eval e), decide_eq_true (p := observed = eval e)⟩

end AeProperty
