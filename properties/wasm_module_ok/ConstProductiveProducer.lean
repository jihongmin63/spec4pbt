import properties.wasm_module_ok.ConstProductiveClosure
import properties.wasm_module_ok.ConstStructExplicitProducer
import properties.wasm_module_ok.ConstStructImplicitProducer
import properties.wasm_module_ok.ConstArrayFixedZeroProducer
import properties.wasm_module_ok.ConstExternConvertProducer

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstProductiveProducer

/-- Every output added by the productive step has a stack-parametric constant
instruction trace in a validated, Bot-free context. -/
theorem productive_step_produces
    (c : SpecTec.context) (s : Finset SpecTec.valtype)
    (u : SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c)
    (hno : SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse c)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (hsound : ∀ v ∈ s, ConstConstructiveProducer.Produces c v)
    (hstep : u ∈ ConstProductiveClosure.productiveStep c s) :
    ConstConstructiveProducer.Produces c u := by
  let saturated :=
    ConstExtendedMatchSaturation.extendedMatchSaturation c
      (ConstMatchAwareClosure.sourcesOf c s)
  rcases Finset.mem_union.mp hstep with hs | houtput
  · exact hsound u hs
  have hcovered : ConstOutputCoverage.Covered c saturated u :=
    (ConstProductiveClosure.covered_outputs_mem_iff c saturated u).1
      houtput
  cases hcovered with
  | basic h =>
    exact ConstConstructiveProducer.basic_produces c u h
  | structImplicit h =>
    exact ConstStructImplicitProducer.struct_implicit_base_produces c u h
  | array h =>
    exact ConstArrayFixedZeroProducer.zero_array_base_produces c u h
  | i31 h =>
    obtain ⟨_, rfl⟩ := (ConstI31Production.i31_step_iff
      saturated u).1 h
    have hi32 : SpecTec.valtype.NumT .I32T ∈
        ConstLiteralProduction.literalBase c :=
      (ConstLiteralProduction.literal_base_mem_iff c _).2 (by rfl)
    have hbasic : SpecTec.valtype.NumT .I32T ∈
        ConstBasicSeed.basicBase c := by
      simp only [ConstBasicSeed.basicBase, Finset.mem_union]
      exact Or.inl (Or.inl (Or.inl hi32))
    exact ConstConstructiveProducer.i31_produces c
      (ConstConstructiveProducer.basic_produces c _ hbasic)
  | structExplicit h =>
    apply ConstStructExplicitProducer.struct_explicit_produces_of_saturation
      c s u hsub h hsound hready
    · intro a ha
      exact CandidateUniverseReady.candidate_universe_in_table
        c a hprov (hsub ha)
    · intro required hrequired
      exact ConstExtendedCandidateReady.extended_candidate_in_table
        c hprov hnested required
        ((ConstExtendedMatchSaturation.extended_match_saturation_mem_iff
          c (ConstMatchAwareClosure.sourcesOf c s) required).1
          hrequired).1
  | externConvert h =>
    exact ConstExternConvertProducer.extern_saturated_step_produces
      c s u hsub hno hready hprov hnested hsound h

theorem productive_iterate_produces
    (c : SpecTec.context)
    (hno : SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse c)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (round : Nat) (u : SpecTec.valtype)
    (hu : u ∈ FiniteClosure.iterate
      (ConstProductiveClosure.productiveStep c) round) :
    ConstConstructiveProducer.Produces c u := by
  induction round generalizing u with
  | zero =>
    simp [FiniteClosure.iterate] at hu
  | succ round ih =>
    exact productive_step_produces c
      (FiniteClosure.iterate (ConstProductiveClosure.productiveStep c)
        round) u
      (FiniteClosure.iterate_bounded
        (FiniteValidTypes.candidateUniverse c)
        (ConstProductiveClosure.productiveStep c)
        (ConstProductiveClosure.productive_step_bounded c) round)
      hno hready hprov hnested
      (fun v hv => ih v hv) hu

end properties.wasm_module_ok.ConstProductiveProducer
