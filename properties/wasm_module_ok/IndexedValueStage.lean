import properties.wasm_module_ok.IndexedListStage

set_option autoImplicit false

namespace properties.wasm_module_ok.IndexedValueStage

def candidates {α : Type} [Encodable α]
    (valid : α → Bool) (n : Nat) : List α :=
  (Enumeration.decodeCandidates (α := α) n).filter valid

theorem candidates_mono {α : Type} [Encodable α]
    (valid : α → Bool) (n k : Nat) (a : α)
    (h : a ∈ candidates valid n) :
    a ∈ candidates valid (n + k) := by
  simp only [candidates, List.mem_filter] at h ⊢
  exact ⟨Enumeration.decodeCandidates_mono n k a h.1, h.2⟩

def generate {α : Type} [Encodable α]
    (valid : α → Bool) : Gen α :=
  Gen.indexed (fun n =>
    IndexedListStage.chooseList (candidates valid n))

theorem generate_support_iff {α : Type} [Encodable α]
    (valid : α → Bool) (a : α) :
    Gen.support (generate valid) a ↔ valid a = true := by
  rw [generate, Gen.Support.support_indexed]
  constructor
  · rintro ⟨_, n, hn⟩
    have hm := (IndexedListStage.chooseList_support_some
      (candidates valid n) a).mp hn
    exact (List.mem_filter.mp hm).2
  · intro hv
    constructor
    · intro b n k hn
      apply (IndexedListStage.chooseList_support_some
        (candidates valid (n + k)) b).2
      exact candidates_mono valid n k b
        ((IndexedListStage.chooseList_support_some
          (candidates valid n) b).1 hn)
    · obtain ⟨n, hn⟩ := Enumeration.decodeCandidates_complete a
      exact ⟨n, (IndexedListStage.chooseList_support_some
        (candidates valid n) a).2
        ((List.mem_filter).2 ⟨hn, hv⟩)⟩

def correct {α : Type} [Encodable α]
    (valid : α → Bool) : CorrectGen (fun a : α => valid a = true) := by
  refine ⟨generate valid, ?_⟩
  funext a
  exact propext (generate_support_iff valid a)

end properties.wasm_module_ok.IndexedValueStage
