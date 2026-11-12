import Spec4Pbt.CorrectGen
import properties.wasm_module_ok.Enumeration

set_option autoImplicit false

namespace properties.wasm_module_ok.IndexedListStage

def chooseList {α : Type} : List α → Gen (Option α)
  | [] => pure none
  | a :: rest => Gen.pick (pure (some a)) (chooseList rest)

theorem chooseList_support_some {α : Type}
    (xs : List α) (a : α) :
    Gen.support (chooseList xs) (some a) ↔ a ∈ xs := by
  induction xs with
  | nil => simp [chooseList]
  | cons head rest ih => simp [chooseList, ih]

def candidates {α : Type} [Encodable α]
    (valid : List α → Bool) (n : Nat) : List (List α) :=
  (Enumeration.decodeCandidates (α := List α) n).filter valid

theorem candidates_mono {α : Type} [Encodable α]
    (valid : List α → Bool) (n k : Nat) (xs : List α)
    (h : xs ∈ candidates valid n) :
    xs ∈ candidates valid (n + k) := by
  simp only [candidates, List.mem_filter] at h ⊢
  exact ⟨Enumeration.decodeCandidates_mono n k xs h.1, h.2⟩

def generate {α : Type} [Encodable α]
    (valid : List α → Bool) : Gen (List α) :=
  Gen.indexed (fun n => chooseList (candidates valid n))

theorem generate_support_iff {α : Type} [Encodable α]
    (valid : List α → Bool) (xs : List α) :
    Gen.support (generate valid) xs ↔ valid xs = true := by
  rw [generate, Gen.Support.support_indexed]
  constructor
  · rintro ⟨_, n, hn⟩
    have hm := (chooseList_support_some (candidates valid n) xs).mp hn
    exact (List.mem_filter.mp hm).2
  · intro hv
    constructor
    · intro ys n k hn
      apply (chooseList_support_some (candidates valid (n + k)) ys).2
      exact candidates_mono valid n k ys
        ((chooseList_support_some (candidates valid n) ys).1 hn)
    · obtain ⟨n, hn⟩ := Enumeration.decodeCandidates_complete xs
      exact ⟨n, (chooseList_support_some (candidates valid n) xs).2
        ((List.mem_filter).2 ⟨hn, hv⟩)⟩

theorem generate_nonempty_of_valid_nil {α : Type} [Encodable α]
    (valid : List α → Bool) (h : valid [] = true) :
    Gen.support (generate valid) [] :=
  (generate_support_iff valid []).2 h

def correct {α : Type} [Encodable α]
    (valid : List α → Bool) :
    CorrectGen (fun xs : List α => valid xs = true) := by
  refine ⟨generate valid, ?_⟩
  funext xs
  exact propext (generate_support_iff valid xs)

end properties.wasm_module_ok.IndexedListStage
