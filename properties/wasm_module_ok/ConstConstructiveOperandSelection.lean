import properties.wasm_module_ok.ConstConstructiveMatchList
import properties.wasm_module_ok.ConstMatchAwareClosure

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstConstructiveOperandSelection

/-- A saturated requirement list has an ordered source witness for every
position, including repeated requirements. -/
theorem select_sources
    (c : SpecTec.context) (sources required : List SpecTec.valtype)
    (hall : ∀ r ∈ required,
      r ∈ ConstExtendedMatchSaturation.extendedMatchSaturation c sources) :
    ∃ actual : List SpecTec.valtype,
      (∀ a ∈ actual, a ∈ sources) ∧
      List.Forall₂
        (fun a r => CandidateValMatch.candidateValMatch c a r = true)
        actual required := by
  induction required with
  | nil =>
    exact ⟨[], by simp, List.Forall₂.nil⟩
  | cons r rest ih =>
    obtain ⟨_, a, ha, hmatch⟩ :=
      (ConstExtendedMatchSaturation.extended_match_saturation_mem_iff
        c sources r).1 (hall r (by simp))
    obtain ⟨actual, hsource, hpairs⟩ :=
      ih (by
        intro v hv
        exact hall v (by simp [hv]))
    refine ⟨a :: actual, ?_, List.Forall₂.cons hmatch hpairs⟩
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact ha
    · exact hsource v hv

theorem select_closure_sources
    (c : SpecTec.context) (s : Finset SpecTec.valtype)
    (required : List SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c)
    (hall : ∀ r ∈ required,
      r ∈ ConstExtendedMatchSaturation.extendedMatchSaturation c
        (ConstMatchAwareClosure.sourcesOf c s)) :
    ∃ actual : List SpecTec.valtype,
      (∀ a ∈ actual, a ∈ s) ∧
      List.Forall₂
        (fun a r => CandidateValMatch.candidateValMatch c a r = true)
        actual required := by
  obtain ⟨actual, hsource, hpairs⟩ :=
    select_sources c (ConstMatchAwareClosure.sourcesOf c s) required hall
  refine ⟨actual, ?_, hpairs⟩
  intro a ha
  exact (ConstMatchAwareClosure.sources_of_mem_iff c s a hsub).1
    (hsource a ha)

/-- The selected operands have the actual translated ordered stack match. -/
theorem select_closure_sources_with_match
    (c : SpecTec.context) (s : Finset SpecTec.valtype)
    (required : List SpecTec.valtype) (n : Nat)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c)
    (hall : ∀ r ∈ required,
      r ∈ ConstExtendedMatchSaturation.extendedMatchSaturation c
        (ConstMatchAwareClosure.sourcesOf c s))
    (hready : CandidateTypeReady.Ready c)
    (hsourceTable : ∀ a ∈ s, CandidateValMatch.InTableVal c a)
    (hrequiredTable : ∀ r ∈ required,
      CandidateValMatch.InTableVal c r) :
    ∃ actual : List SpecTec.valtype,
      (∀ a ∈ actual, a ∈ s) ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Match_resulttype c
          actual required⟩)
        n (.success (.of ())) n := by
  obtain ⟨actual, hmem, hpairs⟩ :=
    select_closure_sources c s required hsub hall
  refine ⟨actual, hmem, ?_⟩
  exact ConstConstructiveMatchList.match_resulttype_of_pairs
    c actual required n hready hpairs
    (by
      intro a ha
      exact hsourceTable a (hmem a ha))
    hrequiredTable

end properties.wasm_module_ok.ConstConstructiveOperandSelection
