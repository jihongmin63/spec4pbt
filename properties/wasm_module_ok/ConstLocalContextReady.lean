import properties.wasm_module_ok.ConstTraceNestedReady
import properties.wasm_module_ok.ConstMatchReadyStatic

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstLocalContextReady

/-- Local initialization preserves the provenance of function and global
types used by the finite candidate universe. -/
theorem init_locals_provenance
    (c d : SpecTec.context) (indices : List SpecTec.idx)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c indices⟩)
      start (.success (.of d)) finish)
    (hprov : CandidateUniverseReady.Provenance c) :
    CandidateUniverseReady.Provenance d := by
  obtain ⟨ht, hf, hg, _⟩ :=
    LocalInitStatic.init_locals_static_fields c d indices
      start finish hcall
  constructor
  · intro dt hfun
    rw [hf] at hfun
    rw [ht]
    exact hprov.funcs dt hfun
  · intro gt hglobal
    rw [hg] at hglobal
    exact CandidateProvenanceSteps.in_table_val_of_types_eq
      c d _ ht (hprov.globals gt hglobal)

/-- The nested lookup table depends only on TYPES, which `$init_locals`
preserves. -/
theorem init_locals_nested_table_ready
    (c d : SpecTec.context) (indices : List SpecTec.idx)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c indices⟩)
      start (.success (.of d)) finish)
    (hready : CandidateNestedReady.nestedTableReady c = true) :
    CandidateNestedReady.nestedTableReady d = true := by
  have ht := (LocalInitStatic.init_locals_static_fields
    c d indices start finish hcall).1
  rw [← ConstTraceNestedReady.nested_table_ready_of_types_eq c d ht.symm]
  exact hready

end properties.wasm_module_ok.ConstLocalContextReady
