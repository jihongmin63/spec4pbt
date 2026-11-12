import properties.wasm_module_ok.ConstStructImplicitClosure
import properties.wasm_module_ok.ConstStructExplicitProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStructExplicitClosure

/-- A partial production step including explicit struct construction. -/
def structExplicitClosureStep (c : SpecTec.context)
    (s : Finset SpecTec.valtype) : Finset SpecTec.valtype :=
  ConstStructImplicitClosure.structImplicitStep c s ∪
    ConstStructExplicitProduction.structExplicitOutputs c s

theorem struct_explicit_closure_step_bounded (c : SpecTec.context)
    (s : Finset SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c) :
    structExplicitClosureStep c s ⊆ FiniteValidTypes.candidateUniverse c := by
  intro u hu
  rcases Finset.mem_union.mp hu with hprior | hstruct
  · exact ConstStructImplicitClosure.struct_implicit_step_bounded c s hsub hprior
  · exact (Finset.mem_filter.mp hstruct).1

theorem struct_explicit_closure_step_inflate (c : SpecTec.context)
    (s : Finset SpecTec.valtype) :
    s ⊆ structExplicitClosureStep c s := by
  intro u hu
  exact Finset.mem_union_left _
    (ConstStructImplicitClosure.struct_implicit_step_inflate c s hu)

theorem struct_explicit_closure_step_mono (c : SpecTec.context)
    (s t : Finset SpecTec.valtype) (hsub : s ⊆ t) :
    structExplicitClosureStep c s ⊆ structExplicitClosureStep c t := by
  intro u hu
  rcases Finset.mem_union.mp hu with hprior | hstruct
  · exact Finset.mem_union_left _
      (ConstStructImplicitClosure.struct_implicit_step_mono c s t hsub hprior)
  · exact Finset.mem_union_right _
      (ConstStructExplicitProduction.struct_explicit_outputs_mono
        c s t hsub hstruct)

theorem struct_explicit_closure_step_fixed_at_card (c : SpecTec.context) :
    FiniteClosure.iterate (structExplicitClosureStep c)
        (FiniteValidTypes.candidateUniverse c).card =
      FiniteClosure.iterate (structExplicitClosureStep c)
        ((FiniteValidTypes.candidateUniverse c).card + 1) := by
  exact FiniteClosure.iterate_fixed_at_card
    (FiniteValidTypes.candidateUniverse c) (structExplicitClosureStep c)
    (struct_explicit_closure_step_bounded c)
    (fun s _ => struct_explicit_closure_step_inflate c s)

end properties.wasm_module_ok.ConstStructExplicitClosure
