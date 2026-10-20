import specifications.Example

/-!
Arithmetic equivalence between the modulo specification and double naturals.
The local `ite` lemmas below restore two names absent from Lean 4.31.
-/

namespace Example

/- Lean 4.31 has no `ite_eq_left`/`ite_eq_right` convenience lemmas. -/
private theorem ite_eq_left {p : Prop} [Decidable p] {a b : α} (hp : p) :
    (if p then a else b) = a := by simp [hp]

private theorem ite_eq_right {p : Prop} [Decidable p] {a b : α} (hp : ¬p) :
    (if p then a else b) = b := by simp [hp]

private theorem modCoreGo_fuel_congr (x y fuel1 fuel2 : Nat)
    (hy : 0 < y) (h1 : x < fuel1) (h2 : x < fuel2) :
    Nat.modCore.go y hy fuel1 x h1 = Nat.modCore.go y hy fuel2 x h2 := by
  match fuel1, fuel2 with
  | 0, _ => contradiction
  | _, 0 => contradiction
  | fuel1 + 1, fuel2 + 1 =>
    simp only [Nat.modCore.go]
    split
    next => rw [modCoreGo_fuel_congr]
    next => rfl
termination_by structural fuel1

private theorem modCore_eq_step (x y : Nat) : Nat.modCore x y =
    if 0 < y ∧ y ≤ x then Nat.modCore (x - y) y else x := by
  unfold Nat.modCore
  split
  next hy =>
    rw [Nat.modCore.go]
    split
    next h =>
      rw [ite_eq_left (show 0 < y ∧ y ≤ x from ⟨hy, h⟩)]
      apply modCoreGo_fuel_congr
    next h =>
      rw [ite_eq_right (show ¬(0 < y ∧ y ≤ x) from fun hp => h hp.2)]
  next hy =>
    rw [ite_eq_right (show ¬(0 < y ∧ y ≤ x) from fun hp => hy hp.1)]

private theorem modCore_eq_mod (n m : Nat) : Nat.modCore n m = n % m := by
  change Nat.modCore n m = Nat.mod n m
  match n, m with
  | 0, _ =>
    rw [modCore_eq_step]
    exact ite_eq_right fun ⟨hlt, hle⟩ =>
      Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hlt hle)
  | (_ + 1), _ =>
    rw [Nat.mod]
    dsimp
    refine iteInduction (fun _ => rfl) (fun h => ?_)
    rw [modCore_eq_step]
    exact ite_eq_right fun ⟨_, hle⟩ => h hle

private theorem mod_eq_step (x y : Nat) :
    x % y = if 0 < y ∧ y ≤ x then (x - y) % y else x := by
  rw [← modCore_eq_mod, ← modCore_eq_mod, modCore_eq_step]

private theorem mod_two_step (n : Nat) : (n + 2) % 2 = n % 2 := by
  rw [mod_eq_step (n + 2) 2]
  have hp : 0 < 2 ∧ 2 ≤ n + 2 :=
    ⟨by decide, Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))⟩
  rw [ite_eq_left hp]
  rfl

private theorem one_ne_double (k : Nat) : 1 ≠ 2 * k := by
  cases k with
  | zero =>
    intro h
    cases h
  | succ k =>
    intro h
    change Nat.succ 0 = Nat.succ (Nat.succ (2 * k)) at h
    have impossible : (0 : Nat) = Nat.succ (2 * k) := Nat.succ.inj h
    nomatch impossible

private theorem twoStep {P : Nat → Prop} (h0 : P 0) (h1 : P 1)
    (hs : ∀ n, P n → P (n + 2)) : ∀ n, P n := by
  intro n
  have all : ∀ k, P k ∧ P (k + 1) := by
    intro k
    induction k with
    | zero => exact ⟨h0, h1⟩
    | succ k ih => exact ⟨ih.2, hs k ih.1⟩
  exact (all n).1

theorem valid_iff_double (n : Nat) :
    ExampleSpec.Valid n ↔ ∃ k, n = 2 * k := by
  unfold ExampleSpec.Valid
  refine twoStep (P := fun n => n % 2 = 0 ↔ ∃ k, n = 2 * k) ?_ ?_ ?_ n
  · constructor
    · intro _
      exact ⟨0, rfl⟩
    · intro _
      rfl
  · constructor
    · intro h
      have hne : (1 : Nat) % 2 ≠ 0 := by decide
      exact False.elim (hne h)
    · rintro ⟨k, hk⟩
      exact False.elim (one_ne_double k hk)
  · intro n ih
    constructor
    · intro hv
      have hn : n % 2 = 0 := (mod_two_step n).symm.trans hv
      obtain ⟨k, hk⟩ := ih.mp hn
      refine ⟨k + 1, ?_⟩
      change n + 2 = 2 * k + 2
      exact congrArg (· + 2) hk
    · rintro ⟨k, hk⟩
      cases k with
      | zero => cases hk
      | succ k =>
        change n + 2 = 2 * k + 2 at hk
        have hn : n = 2 * k := Nat.succ.inj (Nat.succ.inj hk)
        exact (mod_two_step n).trans (ih.mpr ⟨k, hn⟩)


end Example
