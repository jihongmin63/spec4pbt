import properties.wasm_module_ok.ConstProductiveClosure
import properties.wasm_module_ok.ConstClosureStatic

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstProductiveStatic

theorem covered_outputs_of_static_fields
    (c d : SpecTec.context) (s : Finset SpecTec.valtype)
    (ht : c.TYPES = d.TYPES)
    (hf : c.FUNCS = d.FUNCS)
    (hg : c.GLOBALS = d.GLOBALS)
    (hr : c.REFS = d.REFS) :
    ConstProductiveClosure.coveredOutputs c s =
      ConstProductiveClosure.coveredOutputs d s := by
  have hu := ConstClosureStatic.candidate_universe_of_static_fields
    c d ht hf hg
  have hi31 : ConstI31Production.i31Outputs c s =
      ConstI31Production.i31Outputs d s := by
    simp only [ConstI31Production.i31Outputs, hu]
  have harray : ConstArrayFixedZeroProduction.arrayFixedZeroBase c =
      ConstArrayFixedZeroProduction.arrayFixedZeroBase d := by
    have hseed : ConstArrayFixedZeroProduction.arrayFixedZeroSeed c =
        ConstArrayFixedZeroProduction.arrayFixedZeroSeed d := by
      funext u
      exact ConstClosureStatic.array_fixed_zero_seed_of_types_eq c d ht u
    simp only [ConstArrayFixedZeroProduction.arrayFixedZeroBase, hu, hseed]
  have himplicit : ConstStructImplicitProduction.structImplicitBase c =
      ConstStructImplicitProduction.structImplicitBase d := by
    have hseed : ConstStructImplicitProduction.structImplicitSeed c =
        ConstStructImplicitProduction.structImplicitSeed d := by
      funext u
      exact ConstClosureStatic.struct_implicit_seed_of_types_eq c d ht u
    simp only [ConstStructImplicitProduction.structImplicitBase, hu, hseed]
  have hexplicit : ConstStructExplicitProduction.structExplicitOutputs c s =
      ConstStructExplicitProduction.structExplicitOutputs d s := by
    have hstep : ConstStructExplicitProduction.structExplicitStep c s =
        ConstStructExplicitProduction.structExplicitStep d s := by
      funext u
      exact ConstClosureStatic.struct_explicit_step_of_types_eq
        c d ht s u
    simp only [ConstStructExplicitProduction.structExplicitOutputs, hu, hstep]
  have hextern : ConstExternConvertProduction.externTypeOutputs c s =
      ConstExternConvertProduction.externTypeOutputs d s := by
    simp only [ConstExternConvertProduction.externTypeOutputs, hu]
  simp only [ConstProductiveClosure.coveredOutputs,
    ConstClosureStatic.basic_base_of_static_fields c d ht hf hg hr,
    himplicit, harray, hi31, hexplicit, hextern]

theorem productive_step_of_static_fields
    (c d : SpecTec.context)
    (ht : c.TYPES = d.TYPES)
    (hf : c.FUNCS = d.FUNCS)
    (hg : c.GLOBALS = d.GLOBALS)
    (hr : c.REFS = d.REFS) :
    ConstProductiveClosure.productiveStep c =
      ConstProductiveClosure.productiveStep d := by
  funext s
  have hsources :=
    ConstClosureStatic.sources_of_static_fields c d s ht hf hg
  have hsat :
      ConstExtendedMatchSaturation.extendedMatchSaturation c
          (ConstMatchAwareClosure.sourcesOf c s) =
        ConstExtendedMatchSaturation.extendedMatchSaturation d
          (ConstMatchAwareClosure.sourcesOf d s) := by
    rw [hsources]
    exact ConstClosureStatic.extended_match_saturation_of_static_fields
      c d _ ht hf hg
  change s ∪ ConstProductiveClosure.coveredOutputs c
      (ConstExtendedMatchSaturation.extendedMatchSaturation c
        (ConstMatchAwareClosure.sourcesOf c s)) =
    s ∪ ConstProductiveClosure.coveredOutputs d
      (ConstExtendedMatchSaturation.extendedMatchSaturation d
        (ConstMatchAwareClosure.sourcesOf d s))
  rw [hsat]
  rw [covered_outputs_of_static_fields c d _ ht hf hg hr]

theorem productive_iterate_of_static_fields
    (c d : SpecTec.context)
    (ht : c.TYPES = d.TYPES)
    (hf : c.FUNCS = d.FUNCS)
    (hg : c.GLOBALS = d.GLOBALS)
    (hr : c.REFS = d.REFS) (round : Nat) :
    FiniteClosure.iterate (ConstProductiveClosure.productiveStep c) round =
      FiniteClosure.iterate (ConstProductiveClosure.productiveStep d) round := by
  rw [productive_step_of_static_fields c d ht hf hg hr]

end properties.wasm_module_ok.ConstProductiveStatic
