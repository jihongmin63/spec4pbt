import properties.wasm_module_ok.ConstStructExplicitClosure
import properties.wasm_module_ok.ConstExternConvertProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExternConvertClosure

/-- A partial production step including extern reference conversion. -/
def externClosureStep (c : SpecTec.context)
    (s : Finset SpecTec.valtype) : Finset SpecTec.valtype :=
  ConstStructExplicitClosure.structExplicitClosureStep c s ∪
    ConstExternConvertProduction.externTypeOutputs c s

theorem extern_closure_step_bounded (c : SpecTec.context)
    (s : Finset SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c) :
    externClosureStep c s ⊆ FiniteValidTypes.candidateUniverse c := by
  intro u hu
  rcases Finset.mem_union.mp hu with hprior | hextern
  · exact ConstStructExplicitClosure.struct_explicit_closure_step_bounded
      c s hsub hprior
  · exact (Finset.mem_filter.mp hextern).1

theorem extern_closure_step_inflate (c : SpecTec.context)
    (s : Finset SpecTec.valtype) :
    s ⊆ externClosureStep c s := by
  intro u hu
  exact Finset.mem_union_left _
    (ConstStructExplicitClosure.struct_explicit_closure_step_inflate c s hu)

theorem extern_closure_step_mono (c : SpecTec.context)
    (s t : Finset SpecTec.valtype) (hsub : s ⊆ t) :
    externClosureStep c s ⊆ externClosureStep c t := by
  intro u hu
  rcases Finset.mem_union.mp hu with hprior | hextern
  · exact Finset.mem_union_left _
      (ConstStructExplicitClosure.struct_explicit_closure_step_mono
        c s t hsub hprior)
  · exact Finset.mem_union_right _
      (ConstExternConvertProduction.extern_type_outputs_mono
        c s t hsub hextern)

theorem extern_closure_step_fixed_at_card (c : SpecTec.context) :
    FiniteClosure.iterate (externClosureStep c)
        (FiniteValidTypes.candidateUniverse c).card =
      FiniteClosure.iterate (externClosureStep c)
        ((FiniteValidTypes.candidateUniverse c).card + 1) := by
  exact FiniteClosure.iterate_fixed_at_card
    (FiniteValidTypes.candidateUniverse c) (externClosureStep c)
    (extern_closure_step_bounded c)
    (fun s _ => extern_closure_step_inflate c s)

end properties.wasm_module_ok.ConstExternConvertClosure
