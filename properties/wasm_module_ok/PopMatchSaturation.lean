import properties.wasm_module_ok.PopMatchEntries
import properties.wasm_module_ok.CandidateValMatch
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.PopMatchSaturation

theorem value_matches_iff_candidate
    (c : SpecTec.context) (actual required : SpecTec.valtype)
    (hready : CandidateTypeReady.Ready c)
    (hactual : CandidateValMatch.InTableVal c actual)
    (hrequired : CandidateValMatch.InTableVal c required) :
    PopMatchEntries.ValueMatches c actual required ↔
      CandidateValMatch.candidateValMatch c actual required = true := by
  constructor
  · rintro ⟨start, finish, hmatch⟩
    exact ((CandidateValMatch.candidate_val_match_iff
      c actual required true start finish hready hactual hrequired).1 hmatch).1.symm
  · intro hmatch
    refine ⟨0, 0, ?_⟩
    simpa [hmatch] using
      (CandidateValMatch.candidate_val_match_total
        c actual required 0 hready hactual hrequired)

/-- Executable match closure over source types, before bounding target types. -/
def matchSaturated (c : SpecTec.context)
    (sources : List SpecTec.valtype) (required : SpecTec.valtype) : Bool :=
  sources.any fun actual =>
    CandidateValMatch.candidateValMatch c actual required

/-- The finite target set is deliberately restricted to the proven candidate universe. -/
def matchSaturation (c : SpecTec.context)
    (sources : List SpecTec.valtype) : Finset SpecTec.valtype :=
  ((FiniteValidTypes.candidateTypes c).filter
    (fun required => matchSaturated c sources required = true)).toFinset

theorem match_saturated_iff
    (c : SpecTec.context) (sources : List SpecTec.valtype)
    (required : SpecTec.valtype) :
    matchSaturated c sources required = true ↔
      ∃ actual ∈ sources,
        CandidateValMatch.candidateValMatch c actual required = true := by
  simp only [matchSaturated, List.any_eq_true]

theorem match_saturation_mem_iff
    (c : SpecTec.context) (sources : List SpecTec.valtype)
    (required : SpecTec.valtype) :
    required ∈ matchSaturation c sources ↔
      required ∈ FiniteValidTypes.candidateUniverse c ∧
      ∃ actual ∈ sources,
        CandidateValMatch.candidateValMatch c actual required = true := by
  simp only [matchSaturation, List.mem_toFinset, List.mem_filter,
    FiniteValidTypes.candidateUniverse, List.mem_toFinset,
    match_saturated_iff, decide_eq_true_eq]

theorem match_saturation_mono
    (c : SpecTec.context) (sources₁ sources₂ : List SpecTec.valtype)
    (hsub : ∀ t ∈ sources₁, t ∈ sources₂) :
    matchSaturation c sources₁ ⊆ matchSaturation c sources₂ := by
  intro required hmem
  obtain ⟨hcandidate, actual, hs, hmatch⟩ :=
    (match_saturation_mem_iff c sources₁ required).1 hmem
  exact (match_saturation_mem_iff c sources₂ required).2
    ⟨hcandidate, actual, hsub actual hs, hmatch⟩

theorem match_saturation_bounded
    (c : SpecTec.context) (sources : List SpecTec.valtype) :
    matchSaturation c sources ⊆ FiniteValidTypes.candidateUniverse c := by
  intro required hmem
  exact ((match_saturation_mem_iff c sources required).1 hmem).1

theorem bot_source_saturates_candidates
    (c : SpecTec.context) (sources : List SpecTec.valtype)
    (hbot : SpecTec.valtype.BotT ∈ sources) :
    matchSaturation c sources = FiniteValidTypes.candidateUniverse c := by
  apply Finset.Subset.antisymm (match_saturation_bounded c sources)
  intro required hcandidate
  apply (match_saturation_mem_iff c sources required).2
  refine ⟨hcandidate, .BotT, hbot, ?_⟩
  rfl

theorem pop_required_mem_saturation
    (c : SpecTec.context)
    (need available sources : List SpecTec.valtype)
    (result : SpecTec.inferresulttype) (start finish : Nat)
    (hpop : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of result)) finish)
    (hready : CandidateTypeReady.Ready c)
    (hsource : ∀ actual ∈ available, actual ∈ sources)
    (hactual : ∀ actual ∈ available,
      CandidateValMatch.InTableVal c actual)
    (hrequired : ∀ required ∈ need,
      CandidateValMatch.InTableVal c required)
    (hcandidate : ∀ required ∈ need,
      required ∈ FiniteValidTypes.candidateUniverse c) :
    ∀ required ∈ need, required ∈ matchSaturation c sources := by
  obtain ⟨_, middle, hmatch⟩ :=
    PopMatchExtraction.pop_noellipses_success_has_match
      c need available result start finish hpop
  have hentries := PopMatchEntries.match_resulttype_entries c
    (available.drop (available.length - need.length)) need
    middle finish hmatch
  intro required hmem
  obtain ⟨actual, hsuffix, hrelation⟩ :=
    PopMatchEntries.entries_source c _ _ hentries required hmem
  have havailable : actual ∈ available := List.mem_of_mem_drop hsuffix
  have hbool := (value_matches_iff_candidate c actual required
    hready (hactual actual havailable) (hrequired required hmem)).1 hrelation
  exact (match_saturation_mem_iff c sources required).2
    ⟨hcandidate required hmem, actual, hsource actual havailable, hbool⟩

end properties.wasm_module_ok.PopMatchSaturation
