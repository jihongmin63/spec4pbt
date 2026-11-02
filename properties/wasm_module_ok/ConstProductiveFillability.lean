import properties.wasm_module_ok.ConstProductiveProducer
import properties.wasm_module_ok.ConstConstructiveMatchList

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false

namespace properties.wasm_module_ok.ConstProductiveFillability

/-- The finite fixed-point candidate of exact constant instruction outputs. -/
def productiveClosure (c : SpecTec.context) : Finset SpecTec.valtype :=
  FiniteClosure.iterate (ConstProductiveClosure.productiveStep c)
    (FiniteValidTypes.candidateUniverse c).card

/-- A target is fillable when an output in the productive closure matches it. -/
def productiveFillable (c : SpecTec.context)
    (t : SpecTec.valtype) : Bool :=
  decide (t ∈ ConstExtendedMatchSaturation.extendedMatchSaturation c
    (ConstMatchAwareClosure.sourcesOf c (productiveClosure c)))

theorem source_mem (c : SpecTec.context)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (hu : u ∈ ConstMatchAwareClosure.sourcesOf c s) : u ∈ s := by
  simp only [ConstMatchAwareClosure.sourcesOf,
    List.mem_filter, decide_eq_true_eq] at hu
  exact hu.2

theorem saturation_const_witness
    (c : SpecTec.context) (s : Finset SpecTec.valtype)
    (t : SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c)
    (hsound : ∀ u ∈ s, ConstConstructiveProducer.Produces c u)
    (hmem : t ∈ ConstExtendedMatchSaturation.extendedMatchSaturation c
      (ConstMatchAwareClosure.sourcesOf c s))
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (htable : CandidateValMatch.InTableVal c t) :
    ∃ (xs : List SpecTec.instr) (n : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
        n (.success (.of ())) n := by
  obtain ⟨_, u, husource, humatch⟩ :=
    (ConstExtendedMatchSaturation.extended_match_saturation_mem_iff
      c (ConstMatchAwareClosure.sourcesOf c s) t).1 hmem
  have huclosure : u ∈ s := source_mem c s u husource
  have hucandidate : u ∈ FiniteValidTypes.candidateUniverse c :=
    hsub huclosure
  have hutable : CandidateValMatch.InTableVal c u :=
    CandidateUniverseReady.candidate_universe_in_table
      c u hprov hucandidate
  have hpairs : List.Forall₂
      (fun a r => CandidateValMatch.candidateValMatch c a r = true)
      [u] [t] := List.Forall₂.cons humatch List.Forall₂.nil
  have hactual : ∀ a ∈ [u], CandidateValMatch.InTableVal c a := by
    intro a ha
    simp only [List.mem_singleton] at ha
    subst a
    exact hutable
  have hrequired : ∀ r ∈ [t], CandidateValMatch.InTableVal c r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact htable
  have hmatch :=
    ConstConstructiveMatchList.match_resulttype_of_pairs
      c [u] [t] 0 hready hpairs
      hactual hrequired
  obtain ⟨xs, hx⟩ :=
    ConstConstructiveProducer.produces_const_of_match
      c u t 0 (hsound u huclosure) hmatch
  exact ⟨xs, 0, hx⟩

theorem productive_round_const_witness
    (c : SpecTec.context) (round : Nat) (t : SpecTec.valtype)
    (hmem : t ∈ ConstExtendedMatchSaturation.extendedMatchSaturation c
      (ConstMatchAwareClosure.sourcesOf c
        (FiniteClosure.iterate
          (ConstProductiveClosure.productiveStep c) round)))
    (hno : SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse c)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (htable : CandidateValMatch.InTableVal c t) :
    ∃ (xs : List SpecTec.instr) (n : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
        n (.success (.of ())) n := by
  exact saturation_const_witness c
    (FiniteClosure.iterate (ConstProductiveClosure.productiveStep c) round) t
    (FiniteClosure.iterate_bounded
      (FiniteValidTypes.candidateUniverse c)
      (ConstProductiveClosure.productiveStep c)
      (ConstProductiveClosure.productive_step_bounded c) round)
    (fun u hu => ConstProductiveProducer.productive_iterate_produces
      c hno hready hprov hnested round u hu)
    hmem hready hprov htable

theorem productive_fillable_const_witness
    (c : SpecTec.context) (t : SpecTec.valtype)
    (hfill : productiveFillable c t = true)
    (hno : SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse c)
    (hready : CandidateTypeReady.Ready c)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (htable : CandidateValMatch.InTableVal c t) :
    ∃ (xs : List SpecTec.instr) (n : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
        n (.success (.of ())) n := by
  have hmem : t ∈ ConstExtendedMatchSaturation.extendedMatchSaturation c
      (ConstMatchAwareClosure.sourcesOf c
        (FiniteClosure.iterate
          (ConstProductiveClosure.productiveStep c)
          (FiniteValidTypes.candidateUniverse c).card)) := by
    simpa only [productiveFillable, productiveClosure,
      decide_eq_true_eq] using hfill
  exact productive_round_const_witness c
    (FiniteValidTypes.candidateUniverse c).card t hmem
    hno hready hprov hnested htable

end properties.wasm_module_ok.ConstProductiveFillability
