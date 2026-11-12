import properties.wasm_module_ok.ConstBasicSeed
import properties.wasm_module_ok.ConstI31Production
import properties.wasm_module_ok.FiniteClosure

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstBasicClosure

/-- A partial constant-production step: basic sources and `REF.I31` only. -/
def basicStep (c : SpecTec.context)
    (s : Finset SpecTec.valtype) : Finset SpecTec.valtype :=
  s ∪ ConstBasicSeed.basicBase c ∪
    ConstI31Production.i31Outputs c s

theorem basic_step_bounded (c : SpecTec.context)
    (s : Finset SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c) :
    basicStep c s ⊆ FiniteValidTypes.candidateUniverse c := by
  intro u hu
  simp only [basicStep, Finset.mem_union] at hu
  rcases hu with ((hs | hbase) | hi31)
  · exact hsub hs
  · exact ConstBasicSeed.basic_base_subset_candidate c hbase
  · exact (Finset.mem_filter.mp hi31).1

theorem basic_step_inflate (c : SpecTec.context)
    (s : Finset SpecTec.valtype) :
    s ⊆ basicStep c s := by
  intro u hu
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hu)

theorem basic_step_mono (c : SpecTec.context)
    (s t : Finset SpecTec.valtype) (hsub : s ⊆ t) :
    basicStep c s ⊆ basicStep c t := by
  intro u hu
  simp only [basicStep, Finset.mem_union] at hu ⊢
  rcases hu with ((hs | hbase) | hi31)
  · exact Or.inl (Or.inl (hsub hs))
  · exact Or.inl (Or.inr hbase)
  · exact Or.inr ((ConstI31Production.i31_outputs_mem_iff c t u).2
      (ConstI31Production.i31_step_mono s t u hsub
        ((ConstI31Production.i31_outputs_mem_iff c s u).1 hi31)))

theorem basic_step_fixed_at_card (c : SpecTec.context) :
    FiniteClosure.iterate (basicStep c)
        (FiniteValidTypes.candidateUniverse c).card =
      FiniteClosure.iterate (basicStep c)
        ((FiniteValidTypes.candidateUniverse c).card + 1) := by
  exact FiniteClosure.iterate_fixed_at_card
    (FiniteValidTypes.candidateUniverse c) (basicStep c)
    (basic_step_bounded c) (fun s _ => basic_step_inflate c s)

end properties.wasm_module_ok.ConstBasicClosure
