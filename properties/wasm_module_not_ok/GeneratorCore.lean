import Palamedes.CorrectGen
import Palamedes.Data.Nat
import Mathlib.Logic.Encodable.Basic

set_option autoImplicit false

namespace properties.wasm_module_not_ok.GeneratorCore

def choices {α : Type} (xs : List α) : Gen (Option α) :=
  xs.foldr (fun x acc => Gen.pick (pure (some x)) acc) (pure none)

theorem support_choices {α : Type} (xs : List α) (a : α) :
    Gen.support (choices xs) (some a) ↔ a ∈ xs := by
  induction xs with
  | nil => simp [choices]
  | cons x xs ih =>
      simp only [choices, List.foldr_cons, Gen.Support.support_pick,
        Gen.Support.support_pure, List.mem_cons, Option.some.injEq] at ih ⊢
      exact or_congr Iff.rfl ih

def indexedFilter {α : Type} (enum : Nat → List α) (keep : α → Bool) : Gen α :=
  Gen.indexed (fun n => choices ((enum n).filter keep))

theorem support_indexedFilter {α : Type}
    (enum : Nat → List α) (keep : α → Bool)
    (hmono : ∀ n k a, a ∈ enum n → a ∈ enum (n + k)) :
    Gen.support (indexedFilter enum keep) =
      fun a => keep a = true ∧ ∃ n, a ∈ enum n := by
  funext a
  apply propext
  simp only [indexedFilter, Gen.Support.support_indexed]
  constructor
  · intro ⟨_, n, hs⟩
    rw [support_choices] at hs
    simp only [List.mem_filter] at hs
    exact ⟨hs.2, ⟨n, hs.1⟩⟩
  · intro ⟨ha, n, hn⟩
    constructor
    · intro v i k hv
      rw [support_choices] at hv ⊢
      simp only [List.mem_filter] at hv ⊢
      exact ⟨hmono i k v hv.1, hv.2⟩
    · refine ⟨n, ?_⟩
      rw [support_choices]
      exact List.mem_filter.mpr ⟨hn, ha⟩

theorem support_indexedFilter_exact {α : Type}
    (enum : Nat → List α) (keep : α → Bool) (P : α → Prop)
    (hmono : ∀ n k a, a ∈ enum n → a ∈ enum (n + k))
    (hcomplete : ∀ a, ∃ n, a ∈ enum n)
    (hkeep : ∀ a, keep a = true ↔ P a) :
    Gen.support (indexedFilter enum keep) = P := by
  funext a
  apply propext
  rw [congrFun (support_indexedFilter enum keep hmono) a]
  constructor
  · intro ⟨ha, _⟩
    exact (hkeep a).mp ha
  · intro ha
    exact ⟨(hkeep a).mpr ha, hcomplete a⟩

def correctIndexedFilter {α : Type}
    (enum : Nat → List α) (keep : α → Bool) (P : α → Prop)
    (hmono : ∀ n k a, a ∈ enum n → a ∈ enum (n + k))
    (hcomplete : ∀ a, ∃ n, a ∈ enum n)
    (hkeep : ∀ a, keep a = true ↔ P a) :
    CorrectGen P :=
  ⟨indexedFilter enum keep,
    support_indexedFilter_exact enum keep P hmono hcomplete hkeep⟩

def encodableFilter {α : Type} [Encodable α] (keep : α → Bool) : Gen α :=
  Gen.arbNat >>= fun n =>
    match Encodable.decode n with
    | none => Gen.assume false (fun h => by cases h)
    | some a => Gen.assume (keep a) (fun _ => pure a)

theorem support_encodableFilter {α : Type} [Encodable α] (keep : α → Bool) :
    Gen.support (encodableFilter keep) = fun a => keep a = true := by
  funext a
  apply propext
  constructor
  · intro h
    simp only [encodableFilter, Gen.Support.support_bind, Gen.support_arbNat] at h
    rcases h with ⟨n, _, hn⟩
    cases hd : (Encodable.decode n : Option α) with
    | none => simp [hd, Gen.Support.support_assume] at hn
    | some b =>
      simp only [hd, Gen.Support.support_assume, Gen.Support.support_pure] at hn
      rcases hn with ⟨hb, hab⟩
      subst a
      exact hb
  · intro ha
    simp only [encodableFilter, Gen.Support.support_bind, Gen.support_arbNat]
    refine ⟨Encodable.encode a, trivial, ?_⟩
    simp [Encodable.encodek, Gen.Support.support_assume, ha]

def correctEncodableFilter {α : Type} [Encodable α]
    (keep : α → Bool) (P : α → Prop)
    (hkeep : ∀ a, keep a = true ↔ P a) : CorrectGen P :=
  ⟨encodableFilter keep, by
    funext a
    apply propext
    rw [congrFun (support_encodableFilter keep) a]
    exact hkeep a⟩

end properties.wasm_module_not_ok.GeneratorCore
