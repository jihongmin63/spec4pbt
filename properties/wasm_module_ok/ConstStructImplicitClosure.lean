import properties.wasm_module_ok.ConstFixedZeroClosure
import properties.wasm_module_ok.ConstStructImplicitProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStructImplicitClosure

/-- A partial production step including defaultable implicit struct creation. -/
def structImplicitStep (c : SpecTec.context)
    (s : Finset SpecTec.valtype) : Finset SpecTec.valtype :=
  ConstFixedZeroClosure.fixedZeroStep c s ∪
    ConstStructImplicitProduction.structImplicitBase c

theorem struct_implicit_step_bounded (c : SpecTec.context)
    (s : Finset SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c) :
    structImplicitStep c s ⊆ FiniteValidTypes.candidateUniverse c := by
  intro u hu
  rcases Finset.mem_union.mp hu with hprior | hstruct
  · exact ConstFixedZeroClosure.fixed_zero_step_bounded c s hsub hprior
  · exact (Finset.mem_filter.mp hstruct).1

theorem struct_implicit_step_inflate (c : SpecTec.context)
    (s : Finset SpecTec.valtype) :
    s ⊆ structImplicitStep c s := by
  intro u hu
  exact Finset.mem_union_left _
    (ConstFixedZeroClosure.fixed_zero_step_inflate c s hu)

theorem struct_implicit_step_mono (c : SpecTec.context)
    (s t : Finset SpecTec.valtype) (hsub : s ⊆ t) :
    structImplicitStep c s ⊆ structImplicitStep c t := by
  intro u hu
  rcases Finset.mem_union.mp hu with hprior | hstruct
  · exact Finset.mem_union_left _
      (ConstFixedZeroClosure.fixed_zero_step_mono c s t hsub hprior)
  · exact Finset.mem_union_right _ hstruct

theorem struct_implicit_step_fixed_at_card (c : SpecTec.context) :
    FiniteClosure.iterate (structImplicitStep c)
        (FiniteValidTypes.candidateUniverse c).card =
      FiniteClosure.iterate (structImplicitStep c)
        ((FiniteValidTypes.candidateUniverse c).card + 1) := by
  exact FiniteClosure.iterate_fixed_at_card
    (FiniteValidTypes.candidateUniverse c) (structImplicitStep c)
    (struct_implicit_step_bounded c)
    (fun s _ => struct_implicit_step_inflate c s)

end properties.wasm_module_ok.ConstStructImplicitClosure
