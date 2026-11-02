import properties.wasm_module_ok.ConstStageEntry
import properties.wasm_module_ok.IndexedListStage

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstSyntaxCandidates

/-- Executable size-indexed enumeration of constant-expression syntax.
`SpecTec.const` is the translated instruction-list type. -/
def constCandidates (n : Nat) : List SpecTec.const :=
  Enumeration.decodeCandidates (α := SpecTec.const) n

theorem const_candidates_mono (n k : Nat) (xs : SpecTec.const)
    (h : xs ∈ constCandidates n) :
    xs ∈ constCandidates (n + k) :=
  Enumeration.decodeCandidates_mono n k xs h

theorem const_candidates_complete (xs : SpecTec.const) :
    ∃ n, xs ∈ constCandidates n :=
  Enumeration.decodeCandidates_complete xs

/-- The syntax source itself has full support. Local `Const_ok` checks will
restrict it inside the constant-expression stage. -/
def syntaxGen : Gen SpecTec.const :=
  Gen.indexed (fun n => IndexedListStage.chooseList (constCandidates n))

theorem syntax_gen_support (xs : SpecTec.const) :
    Gen.support syntaxGen xs := by
  rw [syntaxGen, Gen.Support.support_indexed]
  constructor
  · intro ys n k hn
    apply (IndexedListStage.chooseList_support_some
      (constCandidates (n + k)) ys).2
    exact const_candidates_mono n k ys
      ((IndexedListStage.chooseList_support_some
        (constCandidates n) ys).1 hn)
  · obtain ⟨n, hn⟩ := const_candidates_complete xs
    exact ⟨n, (IndexedListStage.chooseList_support_some
      (constCandidates n) xs).2 hn⟩

end properties.wasm_module_ok.ConstSyntaxCandidates
