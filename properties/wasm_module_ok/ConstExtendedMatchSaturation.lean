import properties.wasm_module_ok.ConstInputCoverage
import properties.wasm_module_ok.PopMatchSaturation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExtendedMatchSaturation

def extendedMatchSaturation (c : SpecTec.context)
    (sources : List SpecTec.valtype) : Finset SpecTec.valtype :=
  ((ConstFieldCandidate.extendedCandidateTypes c).filter
    (fun required => PopMatchSaturation.matchSaturated c sources required = true)).toFinset

theorem extended_match_saturation_mem_iff
    (c : SpecTec.context) (sources : List SpecTec.valtype)
    (required : SpecTec.valtype) :
    required ∈ extendedMatchSaturation c sources ↔
      required ∈ ConstFieldCandidate.extendedCandidateUniverse c ∧
      ∃ actual ∈ sources,
        CandidateValMatch.candidateValMatch c actual required = true := by
  simp only [extendedMatchSaturation, List.mem_toFinset,
    List.mem_filter, ConstFieldCandidate.extendedCandidateUniverse,
    List.mem_toFinset, PopMatchSaturation.match_saturated_iff,
    decide_eq_true_eq]

theorem extended_match_saturation_mono
    (c : SpecTec.context)
    (sources₁ sources₂ : List SpecTec.valtype)
    (hsub : ∀ t ∈ sources₁, t ∈ sources₂) :
    extendedMatchSaturation c sources₁ ⊆
      extendedMatchSaturation c sources₂ := by
  intro required hmem
  obtain ⟨hcandidate, actual, hs, hmatch⟩ :=
    (extended_match_saturation_mem_iff c sources₁ required).1 hmem
  exact (extended_match_saturation_mem_iff c sources₂ required).2
    ⟨hcandidate, actual, hsub actual hs, hmatch⟩

theorem extended_match_saturation_bounded
    (c : SpecTec.context) (sources : List SpecTec.valtype) :
    extendedMatchSaturation c sources ⊆
      ConstFieldCandidate.extendedCandidateUniverse c := by
  intro required hmem
  exact ((extended_match_saturation_mem_iff c sources required).1 hmem).1

theorem old_match_saturation_sub_extended
    (c : SpecTec.context) (sources : List SpecTec.valtype) :
    PopMatchSaturation.matchSaturation c sources ⊆
      extendedMatchSaturation c sources := by
  intro required hmem
  obtain ⟨hcandidate, actual, hs, hmatch⟩ :=
    (PopMatchSaturation.match_saturation_mem_iff c sources required).1 hmem
  exact (extended_match_saturation_mem_iff c sources required).2
    ⟨ConstFieldCandidate.old_candidate_mem_extended c required hcandidate,
      actual, hs, hmatch⟩

theorem pop_required_mem_extended_saturation
    (c : SpecTec.context)
    (need available sources : List SpecTec.valtype)
    (result : SpecTec.inferresulttype) (start finish : Nat)
    (hpop : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of result)) finish)
    (hready : CandidateTypeReady.Ready c)
    (hsource : ∀ actual ∈ available, actual ∈ sources)
    (hactual : ∀ actual ∈ available,
      CandidateValMatch.InTableVal c actual)
    (hrequired : ∀ required ∈ need,
      CandidateValMatch.InTableVal c required)
    (hcandidate : ∀ required ∈ need,
      required ∈ ConstFieldCandidate.extendedCandidateUniverse c) :
    ∀ required ∈ need,
      required ∈ extendedMatchSaturation c sources := by
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
  have hbool := (PopMatchSaturation.value_matches_iff_candidate
    c actual required hready (hactual actual havailable)
    (hrequired required hmem)).1 hrelation
  exact (extended_match_saturation_mem_iff c sources required).2
    ⟨hcandidate required hmem, actual, hsource actual havailable, hbool⟩

theorem const_pop_inputs_in_extended_saturation
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (available sources : List SpecTec.valtype)
    (result : SpecTec.inferresulttype)
    (start middle instructionFinish popStart popFinish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt i⟩)
      middle (.success (.of iit)) instructionFinish)
    (hpop : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (.NoEllipses, iit.1.INS.2) (.NoEllipses, available)⟩)
      popStart (.success (.of result)) popFinish)
    (hready : CandidateTypeReady.Ready c)
    (hsource : ∀ actual ∈ available, actual ∈ sources)
    (hactual : ∀ actual ∈ available,
      CandidateValMatch.InTableVal c actual)
    (hrequired : ∀ required ∈ iit.1.INS.2,
      CandidateValMatch.InTableVal c required) :
    ∀ required ∈ iit.1.INS.2,
      required ∈ extendedMatchSaturation c sources := by
  exact pop_required_mem_extended_saturation c iit.1.INS.2
    available sources result popStart popFinish hpop hready hsource
    hactual hrequired
    (ConstInputCoverage.inputs_candidate_of_is_const
      c irt i iit start middle instructionFinish hconst hcall)

end properties.wasm_module_ok.ConstExtendedMatchSaturation
