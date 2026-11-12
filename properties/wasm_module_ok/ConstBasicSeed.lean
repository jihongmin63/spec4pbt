import properties.wasm_module_ok.ConstLiteralProduction
import properties.wasm_module_ok.ConstRefNullProduction
import properties.wasm_module_ok.ConstRefFuncProduction
import properties.wasm_module_ok.ConstGlobalGetProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstBasicSeed

/-- The currently proved basic constant sources. Constructor rules with empty
inputs are handled separately in the production closure. -/
def basicSeed (c : SpecTec.context) (u : SpecTec.valtype) : Bool :=
  ConstLiteralProduction.literalSeed u ||
    ConstRefNullProduction.refNullSeed c u ||
    ConstRefFuncProduction.refFuncSeed c u ||
    ConstGlobalGetProduction.globalGetSeed c u

def basicBase (c : SpecTec.context) : Finset SpecTec.valtype :=
  ConstLiteralProduction.literalBase c ∪
    ConstRefNullProduction.refNullBase c ∪
    ConstRefFuncProduction.refFuncBase c ∪
    ConstGlobalGetProduction.globalGetBase c

theorem basic_base_mem_iff (c : SpecTec.context)
    (u : SpecTec.valtype) :
    u ∈ basicBase c ↔ basicSeed c u = true := by
  simp only [basicBase, Finset.mem_union,
    ConstLiteralProduction.literal_base_mem_iff,
    ConstRefNullProduction.ref_null_base_mem_iff,
    ConstRefFuncProduction.ref_func_base_mem_iff,
    ConstGlobalGetProduction.global_get_base_mem_iff,
    basicSeed, Bool.or_eq_true]

theorem basic_base_subset_candidate (c : SpecTec.context) :
    basicBase c ⊆ FiniteValidTypes.candidateUniverse c := by
  intro u hu
  simp only [basicBase, Finset.mem_union] at hu
  rcases hu with (((hliteral | hnull) | hfunc) | hglobal)
  · exact (Finset.mem_filter.mp hliteral).1
  · simp only [ConstRefNullProduction.refNullBase,
      List.mem_toFinset, List.mem_map] at hnull
    obtain ⟨ht, hmem, rfl⟩ := hnull
    apply FiniteValidTypes.valid_mem_candidateUniverse
    exact (FiniteValidTypes.heapCandidates_spec c ht).1 hmem
  · exact (Finset.mem_filter.mp hfunc).1
  · exact (Finset.mem_filter.mp hglobal).1

end properties.wasm_module_ok.ConstBasicSeed
