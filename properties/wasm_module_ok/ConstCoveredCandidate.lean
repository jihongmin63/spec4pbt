import properties.wasm_module_ok.ConstClosureOutputCoverage

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstCoveredCandidate

/-- Every production output is in the finite output universe, regardless of
the set used to justify its operands. -/
theorem covered_output_candidate (c : SpecTec.context)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (h : ConstOutputCoverage.Covered c s u) :
    u ∈ FiniteValidTypes.candidateUniverse c := by
  cases h with
  | basic h => exact ConstBasicSeed.basic_base_subset_candidate c h
  | structImplicit h =>
      exact (Finset.mem_filter.mp h).1
  | array h =>
      exact (Finset.mem_filter.mp h).1
  | i31 h =>
      exact (Finset.mem_filter.mp
        ((ConstI31Production.i31_outputs_mem_iff c s u).2 h)).1
  | structExplicit h =>
      exact (Finset.mem_filter.mp
        ((ConstStructExplicitProduction.struct_explicit_outputs_mem_iff
          c s u).2 h)).1
  | externConvert h =>
      exact ConstExternConvertProduction.extern_type_step_output_mem_candidate
        c s u h

end properties.wasm_module_ok.ConstCoveredCandidate
