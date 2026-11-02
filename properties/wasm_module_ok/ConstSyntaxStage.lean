import properties.wasm_module_ok.ConstSyntaxCandidates
import properties.wasm_module_ok.ConstSyntaxDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstSyntaxStage

def syntaxPasses (c : SpecTec.context) (xs : SpecTec.const) : Bool :=
  xs.all (ConstSyntaxDecision.syntaxAllowed c)

theorem syntax_passes_iff (c : SpecTec.context) (xs : SpecTec.const) :
    syntaxPasses c xs = true ↔
      ∀ i ∈ xs, ConstAdditionalSyntaxValidation.Syntax c i := by
  induction xs with
  | nil => simp [syntaxPasses]
  | cons i rest ih =>
    simp [syntaxPasses, ConstSyntaxDecision.syntaxAllowed_iff]

def syntaxCandidates (c : SpecTec.context) (n : Nat) :
    List SpecTec.const :=
  (ConstSyntaxCandidates.constCandidates n).filter (syntaxPasses c)

theorem syntax_candidates_mono (c : SpecTec.context)
    (n k : Nat) (xs : SpecTec.const)
    (h : xs ∈ syntaxCandidates c n) :
    xs ∈ syntaxCandidates c (n + k) := by
  simp only [syntaxCandidates, List.mem_filter] at h ⊢
  exact ⟨ConstSyntaxCandidates.const_candidates_mono n k xs h.1, h.2⟩

def syntaxGen (c : SpecTec.context) : Gen SpecTec.const :=
  Gen.indexed (fun n =>
    IndexedListStage.chooseList (syntaxCandidates c n))

theorem syntax_gen_support_iff
    (c : SpecTec.context) (xs : SpecTec.const) :
    Gen.support (syntaxGen c) xs ↔ syntaxPasses c xs = true := by
  rw [syntaxGen, Gen.Support.support_indexed]
  constructor
  · rintro ⟨_, n, hn⟩
    have hmem := (IndexedListStage.chooseList_support_some
      (syntaxCandidates c n) xs).1 hn
    exact (List.mem_filter.mp hmem).2
  · intro hsyntax
    constructor
    · intro ys n k hn
      apply (IndexedListStage.chooseList_support_some
        (syntaxCandidates c (n + k)) ys).2
      exact syntax_candidates_mono c n k ys
        ((IndexedListStage.chooseList_support_some
          (syntaxCandidates c n) ys).1 hn)
    · obtain ⟨n, hmem⟩ :=
        ConstSyntaxCandidates.const_candidates_complete xs
      exact ⟨n, (IndexedListStage.chooseList_support_some
        (syntaxCandidates c n) xs).2
          ((List.mem_filter).2 ⟨hmem, hsyntax⟩)⟩

theorem syntax_gen_exact
    (c : SpecTec.context) (xs : SpecTec.const) :
    Gen.support (syntaxGen c) xs ↔
      ∀ i ∈ xs, ConstAdditionalSyntaxValidation.Syntax c i := by
  exact (syntax_gen_support_iff c xs).trans (syntax_passes_iff c xs)

end properties.wasm_module_ok.ConstSyntaxStage
