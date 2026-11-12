import properties.wasm_module_ok.ConstCoveredCandidate
import properties.wasm_module_ok.ConstMatchAwareOutputCoverage

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstMatchAwareClosure

/-- Executable representatives of the types already reached. -/
def sourcesOf (c : SpecTec.context) (s : Finset SpecTec.valtype) :
    List SpecTec.valtype :=
  (FiniteValidTypes.candidateTypes c).filter (fun t => decide (t ∈ s))

theorem sources_of_mem_iff (c : SpecTec.context)
    (s : Finset SpecTec.valtype) (t : SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c) :
    t ∈ sourcesOf c s ↔ t ∈ s := by
  simp only [sourcesOf, List.mem_filter, decide_eq_true_eq]
  constructor
  · exact And.right
  · intro ht
    exact ⟨by simpa only [FiniteValidTypes.candidateUniverse,
      List.mem_toFinset] using hsub ht, ht⟩

theorem sources_of_mono (c : SpecTec.context)
    (s t : Finset SpecTec.valtype) (hsub : s ⊆ t) :
    ∀ u ∈ sourcesOf c s, u ∈ sourcesOf c t := by
  intro u hu
  simp only [sourcesOf, List.mem_filter, decide_eq_true_eq] at hu ⊢
  exact ⟨hu.1, hsub hu.2⟩

/-- Match-aware forward closure, retaining only possible output types. -/
def matchAwareStep (c : SpecTec.context)
    (s : Finset SpecTec.valtype) : Finset SpecTec.valtype :=
  s ∪ (FiniteValidTypes.candidateUniverse c).filter
    (fun u => u ∈ ConstExternConvertClosure.externClosureStep c
      (ConstExtendedMatchSaturation.extendedMatchSaturation c (sourcesOf c s)))

theorem match_aware_step_bounded (c : SpecTec.context)
    (s : Finset SpecTec.valtype)
    (hsub : s ⊆ FiniteValidTypes.candidateUniverse c) :
    matchAwareStep c s ⊆ FiniteValidTypes.candidateUniverse c := by
  intro u hu
  rcases Finset.mem_union.mp hu with hs | hp
  · exact hsub hs
  · exact (Finset.mem_filter.mp hp).1

theorem match_aware_step_inflate (c : SpecTec.context)
    (s : Finset SpecTec.valtype) :
    s ⊆ matchAwareStep c s := by
  intro u hu
  exact Finset.mem_union_left _ hu

theorem match_aware_step_mono (c : SpecTec.context)
    (s t : Finset SpecTec.valtype) (hsub : s ⊆ t) :
    matchAwareStep c s ⊆ matchAwareStep c t := by
  intro u hu
  rcases Finset.mem_union.mp hu with hs | hp
  · exact Finset.mem_union_left _ (hsub hs)
  · obtain ⟨hcandidate, hstep⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_union_right
    apply Finset.mem_filter.mpr
    refine ⟨hcandidate, ?_⟩
    exact ConstExternConvertClosure.extern_closure_step_mono c _ _
      (ConstExtendedMatchSaturation.extended_match_saturation_mono
        c _ _ (sources_of_mono c s t hsub)) hstep

theorem match_aware_step_fixed_at_card (c : SpecTec.context) :
    FiniteClosure.iterate (matchAwareStep c)
        (FiniteValidTypes.candidateUniverse c).card =
      FiniteClosure.iterate (matchAwareStep c)
        ((FiniteValidTypes.candidateUniverse c).card + 1) := by
  exact FiniteClosure.iterate_fixed_at_card
    (FiniteValidTypes.candidateUniverse c) (matchAwareStep c)
    (match_aware_step_bounded c)
    (fun s _ => match_aware_step_inflate c s)

/-- A successful constant instruction with a successful pop advances the
finite match-aware closure, without bounding the length of the stack. -/
theorem output_mem_match_aware_step
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (start middle instructionFinish popStart popFinish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt i⟩)
      middle (.success (.of iit)) instructionFinish)
    (hpop : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, iit.1.INS.2) (.NoEllipses, available)⟩)
      popStart (.success (.of result)) popFinish)
    (hbounded : s ⊆ FiniteValidTypes.candidateUniverse c)
    (havailable : ∀ actual ∈ available, actual ∈ s)
    (hready : CandidateTypeReady.Ready c)
    (hactual : ∀ actual ∈ available,
      CandidateValMatch.InTableVal c actual)
    (hrequired : ∀ required ∈ iit.1.INS.2,
      CandidateValMatch.InTableVal c required)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    u ∈ matchAwareStep c s := by
  let sources := sourcesOf c s
  have hsource : ∀ actual ∈ available, actual ∈ sources := by
    intro actual hmem
    exact (sources_of_mem_iff c s actual hbounded).2
      (havailable actual hmem)
  have hinputs :=
    ConstExtendedMatchSaturation.const_pop_inputs_in_extended_saturation
      c irt i iit available sources result
      start middle instructionFinish popStart popFinish
      hconst hcall hpop hready hsource hactual hrequired
  have hsyntax :=
    (ConstSyntaxClassification.is_const_success_iff
      c i start middle).1 hconst |>.1
  have hcandidate : u ∈ FiniteValidTypes.candidateUniverse c :=
    ConstCoveredCandidate.covered_output_candidate c
      (ConstExtendedMatchSaturation.extendedMatchSaturation c sources) u
      (ConstOutputCoverage.covered_of_syntax c irt _ i iit u
        middle instructionFinish hsyntax hcall hinputs houts)
  have hstep :=
    ConstMatchAwareOutputCoverage.output_mem_match_aware_step
      c irt i iit available sources result u
      start middle instructionFinish popStart popFinish
      hconst hcall hpop hready hsource hactual hrequired houts
  exact Finset.mem_union_right _
    (Finset.mem_filter.mpr ⟨hcandidate, hstep⟩)

end properties.wasm_module_ok.ConstMatchAwareClosure
