/-!
A generator is an executable total size/seed sampler. Its support contains every value
reachable for some size and seed. A `CorrectGen P` carries both a generator and
the pointwise proof that its support is exactly `P`.
-/

namespace Spec4Pbt

universe u v

abbrev Generator (α : Type u) := Nat → Nat → α

def Support {α : Type u} (gen : Generator α) (value : α) : Prop :=
  ∃ size seed, gen size seed = value

def CorrectGen {α : Type u} (P : α → Prop) :=
  {gen : Generator α // ∀ value, Support gen value ↔ P value}

private def splitSeed : Nat → Bool × Nat
  | 0 => (true, 0)
  | 1 => (false, 0)
  | n + 2 =>
    let (branch, inner) := splitSeed n
    (branch, inner + 1)

private def leftSeed : Nat → Nat
  | 0 => 0
  | n + 1 => leftSeed n + 2

private def rightSeed : Nat → Nat
  | 0 => 1
  | n + 1 => rightSeed n + 2

private theorem split_left (n : Nat) : splitSeed (leftSeed n) = (true, n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change splitSeed (leftSeed n + 2) = (true, n + 1)
    rw [splitSeed, ih]

private theorem split_right (n : Nat) : splitSeed (rightSeed n) = (false, n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change splitSeed (rightSeed n + 2) = (false, n + 1)
    rw [splitSeed, ih]

private def choose (left right : Generator α) : Generator α :=
  fun size seed =>
    if (splitSeed seed).1 then left size (splitSeed seed).2
    else right size (splitSeed seed).2

private theorem support_choose (left right : Generator α) (value : α) :
    Support (choose left right) value ↔
      Support left value ∨ Support right value := by
  constructor
  · rintro ⟨size, seed, h⟩
    cases hsplit : splitSeed seed with
    | mk branch inner =>
      cases branch
      · right
        dsimp [choose] at h
        rw [hsplit] at h
        exact ⟨size, inner, h⟩
      · left
        dsimp [choose] at h
        rw [hsplit] at h
        exact ⟨size, inner, h⟩
  · intro h
    rcases h with ⟨size, seed, h⟩ | ⟨size, seed, h⟩
    · refine ⟨size, leftSeed seed, ?_⟩
      change (if (splitSeed (leftSeed seed)).1
        then left size (splitSeed (leftSeed seed)).2
        else right size (splitSeed (leftSeed seed)).2) = value
      rw [split_left]
      exact h
    · refine ⟨size, rightSeed seed, ?_⟩
      change (if (splitSeed (rightSeed seed)).1
        then left size (splitSeed (rightSeed seed)).2
        else right size (splitSeed (rightSeed seed)).2) = value
      rw [split_right]
      exact h

/- `bind` needs independent size/seed pairs. Diagonal enumeration encodes the
two natural numbers in one, with a constructive inverse. -/
private def step : Nat × Nat → Nat × Nat
  | (0, y) => (y + 1, 0)
  | (x + 1, y) => (x, y + 1)

private def unpair : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => step (unpair n)

private def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + n + 1

private def pair (x y : Nat) : Nat := triangle (x + y) + y

private theorem diagonal (n : Nat) : ∀ x y : Nat, x + y = n →
    unpair (triangle n + y) = (x, y) := by
  induction n with
  | zero =>
    intro x y h
    cases x with
    | zero =>
      cases y with
      | zero => rfl
      | succ y => cases h
    | succ x =>
      rw [Nat.succ_add] at h
      cases h
  | succ n ih =>
    intro x y h
    induction y generalizing x with
    | zero =>
      have hx : x = n + 1 := by simpa only [Nat.add_zero] using h
      subst x
      have prev : unpair (triangle n + n) = (0, n) := ih 0 n (Nat.zero_add n)
      change step (unpair (triangle n + n)) = (n + 1, 0)
      rw [prev]
      rfl
    | succ y ihy =>
      have hprev : (x + 1) + y = n + 1 := by
        rw [Nat.succ_add]
        exact h
      have prev : unpair (triangle (n + 1) + y) = (x + 1, y) :=
        ihy (x + 1) hprev
      change step (unpair (triangle (n + 1) + y)) = (x, y + 1)
      rw [prev]
      rfl

private theorem unpair_pair (x y : Nat) : unpair (pair x y) = (x, y) :=
  diagonal (x + y) x y rfl

private def bindRaw {α : Type u} {β : Type v}
    (gen : Generator α) (next : α → Generator β) : Generator β :=
  fun size seed =>
    let sizes := unpair size
    let seeds := unpair seed
    next (gen sizes.1 seeds.1) sizes.2 seeds.2

private theorem support_bind {α : Type u} {β : Type v}
    (gen : Generator α) (next : α → Generator β) (result : β) :
    Support (bindRaw gen next) result ↔
      ∃ value, Support gen value ∧ Support (next value) result := by
  constructor
  · rintro ⟨size, seed, h⟩
    exact ⟨gen (unpair size).1 (unpair seed).1,
      ⟨(unpair size).1, (unpair seed).1, rfl⟩,
      ⟨(unpair size).2, (unpair seed).2, h⟩⟩
  · rintro ⟨value, ⟨size1, seed1, outer⟩, ⟨size2, seed2, inner⟩⟩
    refine ⟨pair size1 size2, pair seed1 seed2, ?_⟩
    change next (gen (unpair (pair size1 size2)).1 (unpair (pair seed1 seed2)).1)
      (unpair (pair size1 size2)).2 (unpair (pair seed1 seed2)).2 = result
    rw [unpair_pair size1 size2, unpair_pair seed1 seed2, outer]
    exact inner

namespace CorrectGen

/-- Exact support is equivalent to unconditional sample validity and coverage. -/
theorem exact_support_iff {α : Type u} (gen : Generator α) (P : α → Prop) :
    (∀ value, Support gen value ↔ P value) ↔
      (∀ size seed, P (gen size seed)) ∧
      (∀ value, P value → ∃ size seed, gen size seed = value) := by
  constructor
  · intro h
    exact ⟨fun size seed => (h (gen size seed)).mp ⟨size, seed, rfl⟩,
      fun value valid => (h value).mpr valid⟩
  · rintro ⟨sound, complete⟩ value
    constructor
    · rintro ⟨size, seed, h⟩
      rw [← h]
      exact sound size seed
    · exact complete value

/-- Every invocation of a correct total generator produces a valid value. -/
theorem sound {α : Type u} {P : α → Prop} (gen : CorrectGen P)
    (size seed : Nat) : P (gen.val size seed) :=
  (gen.property (gen.val size seed)).mp ⟨size, seed, rfl⟩

/-- Every valid value occurs at some size and seed. -/
theorem complete {α : Type u} {P : α → Prop} (gen : CorrectGen P)
    (value : α) (valid : P value) : ∃ size seed, gen.val size seed = value :=
  (gen.property value).mpr valid

def bind {α : Type u} {β : Type v} {P : α → Prop} {Q : α → β → Prop}
    (gen : CorrectGen P) (next : ∀ value, CorrectGen (Q value)) :
    CorrectGen (fun result => ∃ value, P value ∧ Q value result) :=
  ⟨bindRaw gen.val (fun value => (next value).val), by
    intro result
    constructor
    · intro h
      obtain ⟨value, hv, hr⟩ :=
        (support_bind gen.val (fun value => (next value).val) result).mp h
      exact ⟨value, (gen.property value).mp hv,
        ((next value).property result).mp hr⟩
    · rintro ⟨value, hv, hr⟩
      apply (support_bind gen.val (fun value => (next value).val) result).mpr
      exact ⟨value, (gen.property value).mpr hv,
        ((next value).property result).mpr hr⟩⟩

def pick {α : Type u} {P Q : α → Prop}
    (left : CorrectGen P) (right : CorrectGen Q) :
    CorrectGen (fun value => P value ∨ Q value) :=
  ⟨choose left.val right.val, by
    intro value
    constructor
    · intro h
      cases (support_choose left.val right.val value).mp h with
      | inl hl => exact Or.inl ((left.property value).mp hl)
      | inr hr => exact Or.inr ((right.property value).mp hr)
    · intro h
      apply (support_choose left.val right.val value).mpr
      cases h with
      | inl hl => exact Or.inl ((left.property value).mpr hl)
      | inr hr => exact Or.inr ((right.property value).mpr hr)⟩

def pure {α : Type u} (value : α) : CorrectGen (fun other => other = value) :=
  ⟨fun _ _ => value, by
    intro other
    constructor
    · rintro ⟨_, _, h⟩
      exact h.symm
    · intro h
      subst other
      exact ⟨0, 0, rfl⟩⟩

def map {α : Type u} {β : Type v} {P : α → Prop}
    (f : α → β) (g : CorrectGen P) :
    CorrectGen (fun result => ∃ value, P value ∧ f value = result) :=
  ⟨fun size seed => f (g.val size seed), by
    intro result
    constructor
    · rintro ⟨size, seed, h⟩
      exact ⟨g.val size seed, g.sound size seed, h⟩
    · rintro ⟨value, hP, hEq⟩
      obtain ⟨size, seed, hSample⟩ := g.complete value hP
      refine ⟨size, seed, ?_⟩
      change f (g.val size seed) = result
      rw [hSample]
      exact hEq⟩

def convert {α : Type u} {P Q : α → Prop}
    (g : CorrectGen P) (h : ∀ value, P value ↔ Q value) : CorrectGen Q :=
  ⟨g.val, fun value => (g.property value).trans (h value)⟩

end CorrectGen

end Spec4Pbt
