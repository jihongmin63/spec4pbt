import properties.wasm_module_ok.ConstBasicClosure
import properties.wasm_module_ok.ConstArrayFixedZeroProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstFixedZeroClosure

/-- A partial production step with the zero-length fixed-array seed. -/
def fixedZeroStep (c : SpecTec.context)
    (s : Finset SpecTec.valtype) : Finset SpecTec.valtype :=
  ConstBasicClosure.basicStep c s ∪
    ConstArrayFixedZeroProduction.arrayFixedZeroBase c

theorem fixed_zero_step_bounded (c : SpecTec.context)
    (s : Finset SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c) :
    fixedZeroStep c s ⊆ FiniteValidTypes.candidateUniverse c := by
  intro u hu
  rcases Finset.mem_union.mp hu with hbasic | hfixed
  · exact ConstBasicClosure.basic_step_bounded c s hsub hbasic
  · exact (Finset.mem_filter.mp hfixed).1

theorem fixed_zero_step_inflate (c : SpecTec.context)
    (s : Finset SpecTec.valtype) :
    s ⊆ fixedZeroStep c s := by
  intro u hu
  exact Finset.mem_union_left _
    (ConstBasicClosure.basic_step_inflate c s hu)

theorem fixed_zero_step_mono (c : SpecTec.context)
    (s t : Finset SpecTec.valtype) (hsub : s ⊆ t) :
    fixedZeroStep c s ⊆ fixedZeroStep c t := by
  intro u hu
  rcases Finset.mem_union.mp hu with hbasic | hfixed
  · exact Finset.mem_union_left _
      (ConstBasicClosure.basic_step_mono c s t hsub hbasic)
  · exact Finset.mem_union_right _ hfixed

theorem fixed_zero_step_fixed_at_card (c : SpecTec.context) :
    FiniteClosure.iterate (fixedZeroStep c)
        (FiniteValidTypes.candidateUniverse c).card =
      FiniteClosure.iterate (fixedZeroStep c)
        ((FiniteValidTypes.candidateUniverse c).card + 1) := by
  exact FiniteClosure.iterate_fixed_at_card
    (FiniteValidTypes.candidateUniverse c) (fixedZeroStep c)
    (fixed_zero_step_bounded c) (fun s _ => fixed_zero_step_inflate c s)

end properties.wasm_module_ok.ConstFixedZeroClosure
