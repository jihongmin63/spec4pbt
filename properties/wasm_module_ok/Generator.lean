import properties.wasm_module_ok.bundle.Contract

-- Generated unfinished obligation: complete this declaration.
namespace properties.wasm_module_ok.Generator

def chooseList {α : Type} : List α → Gen (Option α)
  | [] => pure none
  | x :: xs => Gen.pick (pure (some x)) (chooseList xs)

theorem support_chooseList_some {α : Type} (xs : List α) (a : α) :
    Gen.support (chooseList xs) (some a) ↔ a ∈ xs := by
  induction xs with
  | nil => simp [chooseList]
  | cons x xs ih => simp [chooseList, ih]

theorem support_indexed_chooseList {α : Type}
    (stages : Nat → List α)
    (hmono : ∀ (n k : Nat) (a : α), a ∈ stages n → a ∈ stages (n + k))
    (a : α) :
    Gen.support (Gen.indexed (fun n => chooseList (stages n))) a ↔
      ∃ n, a ∈ stages n := by
  rw [Gen.Support.support_indexed]
  constructor
  · rintro ⟨_, n, hn⟩
    exact ⟨n, (support_chooseList_some (stages n) a).mp hn⟩
  · rintro ⟨n, hn⟩
    constructor
    · intro v i k hi
      apply (support_chooseList_some (stages (i + k)) v).mpr
      exact hmono i k v ((support_chooseList_some (stages i) v).mp hi)
    · exact ⟨n, (support_chooseList_some (stages n) a).mpr hn⟩

theorem support_indexed_filter {α : Type}
    (candidates : Nat → List α) (valid : α → Bool)
    (hmono : ∀ (n k : Nat) (a : α),
      a ∈ candidates n → a ∈ candidates (n + k))
    (a : α) :
    Gen.support
      (Gen.indexed (fun n => chooseList ((candidates n).filter valid))) a ↔
      (∃ n, a ∈ candidates n) ∧ valid a = true := by
  have hstages : ∀ (n k : Nat) (x : α),
      x ∈ (candidates n).filter valid →
      x ∈ (candidates (n + k)).filter valid := by
    intro n k x hx
    simp only [List.mem_filter] at hx ⊢
    exact ⟨hmono n k x hx.1, hx.2⟩
  rw [support_indexed_chooseList
    (fun n => (candidates n).filter valid) hstages a]
  constructor
  · rintro ⟨n, hn⟩
    simp only [List.mem_filter] at hn
    exact ⟨⟨n, hn.1⟩, hn.2⟩
  · rintro ⟨⟨n, hn⟩, hv⟩
    exact ⟨n, (List.mem_filter).mpr ⟨hn, hv⟩⟩

theorem support_indexed_exact {α : Type}
    (P : α → Prop) (candidates : Nat → List α) (valid : α → Bool)
    (hmono : ∀ (n k : Nat) (a : α),
      a ∈ candidates n → a ∈ candidates (n + k))
    (hcomplete : ∀ a : α, ∃ n, a ∈ candidates n)
    (hvalid : ∀ a : α, valid a = true ↔ P a) :
    (Gen.indexed
      (fun n => chooseList ((candidates n).filter valid))).support = P := by
  funext a
  rw [support_indexed_filter candidates valid hmono a]
  simp only [hcomplete a, true_and]
  exact propext (hvalid a)

def generator : properties.wasm_module_ok.bundle.Contract.generatorValue := by
  fail "Fill in the generator obligation before running check"

theorem soundness :
    properties.wasm_module_ok.bundle.Contract.generatorSound generator := by
  fail "Fill in the soundness obligation before running check"

theorem completeness :
    properties.wasm_module_ok.bundle.Contract.generatorComplete generator := by
  fail "Fill in the completeness obligation before running check"

end properties.wasm_module_ok.Generator
