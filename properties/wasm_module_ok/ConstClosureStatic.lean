import properties.wasm_module_ok.ConstLocalContextReady
import properties.wasm_module_ok.ConstMatchAwareClosure

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstClosureStatic

/-- The executable finite list contains only type, function, and global
context data. -/
theorem candidate_types_of_static_fields
    (c d : SpecTec.context)
    (ht : c.TYPES = d.TYPES)
    (hf : c.FUNCS = d.FUNCS)
    (hg : c.GLOBALS = d.GLOBALS) :
    FiniteValidTypes.candidateTypes c =
      FiniteValidTypes.candidateTypes d := by
  simp [FiniteValidTypes.candidateTypes,
    FiniteValidTypes.validCandidates,
    FiniteValidTypes.refCandidates,
    FiniteValidTypes.heapCandidates, ht, hf, hg]

theorem candidate_universe_of_static_fields
    (c d : SpecTec.context)
    (ht : c.TYPES = d.TYPES)
    (hf : c.FUNCS = d.FUNCS)
    (hg : c.GLOBALS = d.GLOBALS) :
    FiniteValidTypes.candidateUniverse c =
      FiniteValidTypes.candidateUniverse d := by
  simp only [FiniteValidTypes.candidateUniverse,
    candidate_types_of_static_fields c d ht hf hg]

/-- `REF.FUNC` adds a fourth static dependency: the free-reference set. -/
theorem basic_base_of_static_fields
    (c d : SpecTec.context)
    (ht : c.TYPES = d.TYPES)
    (hf : c.FUNCS = d.FUNCS)
    (hg : c.GLOBALS = d.GLOBALS)
    (hr : c.REFS = d.REFS) :
    ConstBasicSeed.basicBase c = ConstBasicSeed.basicBase d := by
  have hu := candidate_universe_of_static_fields c d ht hf hg
  simp [ConstBasicSeed.basicBase,
    ConstLiteralProduction.literalBase,
    ConstRefNullProduction.refNullBase,
    ConstRefFuncProduction.refFuncBase,
    ConstRefFuncProduction.refFuncSeed,
    ConstGlobalGetProduction.globalGetBase,
    ConstGlobalGetProduction.globalGetSeed,
    FiniteValidTypes.heapCandidates, hu, ht, hf, hg, hr]

/-- Source enumeration for match saturation is stable under local changes. -/
theorem sources_of_static_fields
    (c d : SpecTec.context) (s : Finset SpecTec.valtype)
    (ht : c.TYPES = d.TYPES)
    (hf : c.FUNCS = d.FUNCS)
    (hg : c.GLOBALS = d.GLOBALS) :
    ConstMatchAwareClosure.sourcesOf c s =
      ConstMatchAwareClosure.sourcesOf d s := by
  simp only [ConstMatchAwareClosure.sourcesOf,
    candidate_types_of_static_fields c d ht hf hg]

/-- The extra field operand universe is determined by the same static data. -/
theorem extended_candidate_types_of_static_fields
    (c d : SpecTec.context)
    (ht : c.TYPES = d.TYPES)
    (hf : c.FUNCS = d.FUNCS)
    (hg : c.GLOBALS = d.GLOBALS) :
    ConstFieldCandidate.extendedCandidateTypes c =
      ConstFieldCandidate.extendedCandidateTypes d := by
  have hstruct : ConstFieldCandidate.structFieldCandidates c =
      ConstFieldCandidate.structFieldCandidates d := by
    simp [ConstFieldCandidate.structFieldCandidates,
      StructTypeDecision.structTypeResult, ht]
  have harray : ConstFieldCandidate.arrayFieldCandidates c =
      ConstFieldCandidate.arrayFieldCandidates d := by
    simp [ConstFieldCandidate.arrayFieldCandidates,
      ArrayTypeDecision.arrayTypeResult, ht]
  simp only [ConstFieldCandidate.extendedCandidateTypes,
    candidate_types_of_static_fields c d ht hf hg, hstruct, harray]

theorem struct_implicit_seed_of_types_eq
    (c d : SpecTec.context) (ht : c.TYPES = d.TYPES)
    (u : SpecTec.valtype) :
    ConstStructImplicitProduction.structImplicitSeed c u =
      ConstStructImplicitProduction.structImplicitSeed d u := by
  simp [ConstStructImplicitProduction.structImplicitSeed,
    StructTypeDecision.structTypeResult, ht]

theorem array_fixed_zero_seed_of_types_eq
    (c d : SpecTec.context) (ht : c.TYPES = d.TYPES)
    (u : SpecTec.valtype) :
    ConstArrayFixedZeroProduction.arrayFixedZeroSeed c u =
      ConstArrayFixedZeroProduction.arrayFixedZeroSeed d u := by
  simp [ConstArrayFixedZeroProduction.arrayFixedZeroSeed,
    ArrayTypeDecision.arrayTypeResult, ht]

theorem struct_explicit_step_of_types_eq
    (c d : SpecTec.context) (ht : c.TYPES = d.TYPES)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) :
    ConstStructExplicitProduction.structExplicitStep c s u =
      ConstStructExplicitProduction.structExplicitStep d s u := by
  simp [ConstStructExplicitProduction.structExplicitStep,
    StructTypeDecision.structTypeResult, ht]

/-- Recursive indexed matching reads the validated type table only. -/
theorem match_index_fuel_of_types_eq
    (c d : SpecTec.context) (ht : c.TYPES = d.TYPES)
    (fuel p q : Nat) :
    ValidatedMatchIndexFuel.matchIndexFuel c fuel p q =
      ValidatedMatchIndexFuel.matchIndexFuel d fuel p q := by
  induction fuel generalizing p q with
  | zero => rfl
  | succ fuel ih =>
    simp [ValidatedMatchIndexFuel.matchIndexFuel, ht, ih]

theorem match_index_of_types_eq
    (c d : SpecTec.context) (ht : c.TYPES = d.TYPES)
    (p q : Nat) :
    ValidatedMatchIndexFuel.matchIndex c p q =
      ValidatedMatchIndexFuel.matchIndex d p q := by
  exact match_index_fuel_of_types_eq c d ht (p + 1) p q

theorem indexed_def_match_of_types_eq
    (c d : SpecTec.context) (ht : c.TYPES = d.TYPES)
    (dt₁ dt₂ : SpecTec.deftype) :
    ReadyMatchHeaptypeIndex.indexedDefMatch c dt₁ dt₂ =
      ReadyMatchHeaptypeIndex.indexedDefMatch d dt₁ dt₂ := by
  simp [ReadyMatchHeaptypeIndex.indexedDefMatch, ht,
    match_index_of_types_eq c d ht]

theorem indexed_heap_match_of_types_eq
    (c d : SpecTec.context) (ht : c.TYPES = d.TYPES)
    (source target : SpecTec.heaptype) :
    ReadyHeapMatchIndexed.indexedHeapMatch c source target =
      ReadyHeapMatchIndexed.indexedHeapMatch d source target := by
  have hindex : ValidatedMatchIndexFuel.matchIndex c =
      ValidatedMatchIndexFuel.matchIndex d := by
    funext p q
    exact match_index_of_types_eq c d ht p q
  have hdef : ReadyMatchHeaptypeIndex.indexedDefMatch c =
      ReadyMatchHeaptypeIndex.indexedDefMatch d := by
    funext dt₁ dt₂
    exact indexed_def_match_of_types_eq c d ht dt₁ dt₂
  simp [ReadyHeapMatchIndexed.indexedHeapMatch, ht, hindex, hdef]

theorem ready_heap_match_of_types_eq
    (c d : SpecTec.context) (ht : c.TYPES = d.TYPES)
    (source target : SpecTec.heaptype) :
    ReadyHeapMatch.readyHeapMatch c source target =
      ReadyHeapMatch.readyHeapMatch d source target := by
  have hvalue : ReadyHeapMatch.indexedValue c =
      ReadyHeapMatch.indexedValue d := by
    funext heap
    cases heap <;> simp [ReadyHeapMatch.indexedValue, ht]
  have hindexed : ReadyHeapMatchIndexed.indexedHeapMatch c =
      ReadyHeapMatchIndexed.indexedHeapMatch d := by
    funext a b
    exact indexed_heap_match_of_types_eq c d ht a b
  simp [ReadyHeapMatch.readyHeapMatch, hvalue, hindexed]

theorem candidate_val_match_of_types_eq
    (c d : SpecTec.context) (ht : c.TYPES = d.TYPES)
    (actual required : SpecTec.valtype) :
    CandidateValMatch.candidateValMatch c actual required =
      CandidateValMatch.candidateValMatch d actual required := by
  have hheap : ReadyHeapMatch.readyHeapMatch c =
      ReadyHeapMatch.readyHeapMatch d := by
    funext a b
    exact ready_heap_match_of_types_eq c d ht a b
  simp [CandidateValMatch.candidateValMatch, hheap]

theorem extended_match_saturation_of_static_fields
    (c d : SpecTec.context) (s : List SpecTec.valtype)
    (ht : c.TYPES = d.TYPES)
    (hf : c.FUNCS = d.FUNCS)
    (hg : c.GLOBALS = d.GLOBALS) :
    ConstExtendedMatchSaturation.extendedMatchSaturation c s =
      ConstExtendedMatchSaturation.extendedMatchSaturation d s := by
  have hmatch : CandidateValMatch.candidateValMatch c =
      CandidateValMatch.candidateValMatch d := by
    funext actual required
    exact candidate_val_match_of_types_eq c d ht actual required
  simp [ConstExtendedMatchSaturation.extendedMatchSaturation,
    PopMatchSaturation.matchSaturated,
    extended_candidate_types_of_static_fields c d ht hf hg, hmatch]

theorem extern_closure_step_of_static_fields
    (c d : SpecTec.context) (s : Finset SpecTec.valtype)
    (ht : c.TYPES = d.TYPES)
    (hf : c.FUNCS = d.FUNCS)
    (hg : c.GLOBALS = d.GLOBALS)
    (hr : c.REFS = d.REFS) :
    ConstExternConvertClosure.externClosureStep c s =
      ConstExternConvertClosure.externClosureStep d s := by
  have hu := candidate_universe_of_static_fields c d ht hf hg
  have hi31 : ConstI31Production.i31Outputs c s =
      ConstI31Production.i31Outputs d s := by
    simp only [ConstI31Production.i31Outputs, hu]
  have harray : ConstArrayFixedZeroProduction.arrayFixedZeroBase c =
      ConstArrayFixedZeroProduction.arrayFixedZeroBase d := by
    have hseed : ConstArrayFixedZeroProduction.arrayFixedZeroSeed c =
        ConstArrayFixedZeroProduction.arrayFixedZeroSeed d := by
      funext u
      exact array_fixed_zero_seed_of_types_eq c d ht u
    simp only [ConstArrayFixedZeroProduction.arrayFixedZeroBase, hu, hseed]
  have himplicit : ConstStructImplicitProduction.structImplicitBase c =
      ConstStructImplicitProduction.structImplicitBase d := by
    have hseed : ConstStructImplicitProduction.structImplicitSeed c =
        ConstStructImplicitProduction.structImplicitSeed d := by
      funext u
      exact struct_implicit_seed_of_types_eq c d ht u
    simp only [ConstStructImplicitProduction.structImplicitBase, hu, hseed]
  have hexplicit : ConstStructExplicitProduction.structExplicitOutputs c s =
      ConstStructExplicitProduction.structExplicitOutputs d s := by
    have hstep : ConstStructExplicitProduction.structExplicitStep c s =
        ConstStructExplicitProduction.structExplicitStep d s := by
      funext u
      exact struct_explicit_step_of_types_eq c d ht s u
    simp only [ConstStructExplicitProduction.structExplicitOutputs, hu, hstep]
  have hextern : ConstExternConvertProduction.externTypeOutputs c s =
      ConstExternConvertProduction.externTypeOutputs d s := by
    simp only [ConstExternConvertProduction.externTypeOutputs, hu]
  simp only [ConstExternConvertClosure.externClosureStep,
    ConstStructExplicitClosure.structExplicitClosureStep,
    ConstStructImplicitClosure.structImplicitStep,
    ConstFixedZeroClosure.fixedZeroStep,
    ConstBasicClosure.basicStep,
    basic_base_of_static_fields c d ht hf hg hr,
    hi31, harray, himplicit, hexplicit, hextern]

/-- The complete match-aware production step depends on four static context
fields, including REFS for `REF.FUNC`. -/
theorem match_aware_step_of_static_fields
    (c d : SpecTec.context)
    (ht : c.TYPES = d.TYPES)
    (hf : c.FUNCS = d.FUNCS)
    (hg : c.GLOBALS = d.GLOBALS)
    (hr : c.REFS = d.REFS) :
    ConstMatchAwareClosure.matchAwareStep c =
      ConstMatchAwareClosure.matchAwareStep d := by
  funext s
  have hu := candidate_universe_of_static_fields c d ht hf hg
  have hsources := sources_of_static_fields c d s ht hf hg
  have hsat : ConstExtendedMatchSaturation.extendedMatchSaturation c
        (ConstMatchAwareClosure.sourcesOf c s) =
      ConstExtendedMatchSaturation.extendedMatchSaturation d
        (ConstMatchAwareClosure.sourcesOf d s) := by
    rw [hsources]
    exact extended_match_saturation_of_static_fields c d _ ht hf hg
  simp only [ConstMatchAwareClosure.matchAwareStep, hu, hsat,
    extern_closure_step_of_static_fields c d _ ht hf hg hr]

theorem init_locals_match_aware_step
    (c d : SpecTec.context) (indices : List SpecTec.idx)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c indices⟩)
      start (.success (.of d)) finish) :
    ConstMatchAwareClosure.matchAwareStep c =
      ConstMatchAwareClosure.matchAwareStep d := by
  obtain ⟨ht, hf, hg, hr⟩ :=
    LocalInitStatic.init_locals_static_fields c d indices start finish hcall
  exact match_aware_step_of_static_fields c d
    ht.symm hf.symm hg.symm hr.symm

theorem init_locals_closure_iterate
    (c d : SpecTec.context) (indices : List SpecTec.idx)
    (start finish round : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c indices⟩)
      start (.success (.of d)) finish) :
    FiniteClosure.iterate (ConstMatchAwareClosure.matchAwareStep c) round =
      FiniteClosure.iterate (ConstMatchAwareClosure.matchAwareStep d) round := by
  rw [init_locals_match_aware_step c d indices start finish hcall]

end properties.wasm_module_ok.ConstClosureStatic
