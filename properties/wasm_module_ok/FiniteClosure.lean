import Mathlib.Data.Finset.Card
import properties.wasm_module_ok.Enumeration

set_option autoImplicit false

namespace properties.wasm_module_ok.FiniteClosure

variable {α : Type} [DecidableEq α]

def iterate (step : Finset α → Finset α) : Nat → Finset α
  | 0 => ∅
  | n + 1 => step (iterate step n)

theorem iterate_bounded (U : Finset α)
    (step : Finset α → Finset α)
    (hbounded : ∀ s, s ⊆ U → step s ⊆ U)
    (n : Nat) : iterate step n ⊆ U := by
  induction n with
  | zero => simp [iterate]
  | succ n ih => exact hbounded _ ih

theorem iterate_step_subset (U : Finset α)
    (step : Finset α → Finset α)
    (hbounded : ∀ s, s ⊆ U → step s ⊆ U)
    (hinflate : ∀ s, s ⊆ U → s ⊆ step s)
    (n : Nat) : iterate step n ⊆ iterate step (n + 1) :=
  hinflate _ (iterate_bounded U step hbounded n)

theorem iterate_fixed_add
    (step : Finset α → Finset α) (n k : Nat)
    (hfixed : iterate step n = iterate step (n + 1)) :
    iterate step (n + k) = iterate step n := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        iterate step (n + (k + 1)) =
            step (iterate step (n + k)) := by simp [iterate, Nat.add_succ]
        _ = step (iterate step n) := congrArg step ih
        _ = iterate step n := hfixed.symm

theorem iterate_fixed_at_card (U : Finset α)
    (step : Finset α → Finset α)
    (hbounded : ∀ s, s ⊆ U → step s ⊆ U)
    (hinflate : ∀ s, s ⊆ U → s ⊆ step s) :
    iterate step U.card =
      iterate step (U.card + 1) := by
  by_contra hne
  have hstrict : ∀ n ≤ U.card,
      (iterate step n).card < (iterate step (n + 1)).card := by
    intro n hn
    have hsets : iterate step n ≠ iterate step (n + 1) := by
      intro heq
      obtain ⟨k, hk⟩ : ∃ k, U.card = n + k :=
        ⟨U.card - n, by omega⟩
      have heqN := iterate_fixed_add step n k heq
      have heqN1 := iterate_fixed_add step n (k + 1) heq
      have : iterate step (U.card + 1) =
          iterate step U.card := by
        calc
          iterate step (U.card + 1) = iterate step n := by
            simpa [hk, Nat.add_assoc] using heqN1
          _ = iterate step U.card := by
            simpa [hk] using heqN.symm
      exact hne this.symm
    exact Finset.card_lt_card
      ((Finset.ssubset_iff_subset_ne).2
        ⟨iterate_step_subset U step hbounded hinflate n, hsets⟩)
  have hlower : ∀ n ≤ U.card + 1,
      n ≤ (iterate step n).card := by
    intro n hn
    induction n with
    | zero => simp
    | succ n ih =>
        have hle : n ≤ U.card := by omega
        have hlt := hstrict n hle
        have hprev : n ≤ (iterate step n).card := ih (by omega)
        omega
  have hupper : (iterate step (U.card + 1)).card ≤
      U.card :=
    Finset.card_le_card
      (iterate_bounded U step hbounded (U.card + 1))
  have := hlower (U.card + 1) (by omega)
  omega

theorem iterate_subset_of_closed
    (step : Finset α → Finset α)
    (hmono : ∀ s t, s ⊆ t → step s ⊆ step t)
    (target : Finset α) (hclosed : step target ⊆ target)
    (n : Nat) : iterate step n ⊆ target := by
  induction n with
  | zero => simp [iterate]
  | succ n ih =>
      exact (hmono _ _ ih).trans hclosed

theorem fixed_at_card_least (U : Finset α)
    (step : Finset α → Finset α)
    (hmono : ∀ s t, s ⊆ t → step s ⊆ step t)
    (target : Finset α) (hclosed : step target ⊆ target) :
    iterate step U.card ⊆ target :=
  iterate_subset_of_closed step hmono target hclosed U.card

end properties.wasm_module_ok.FiniteClosure
