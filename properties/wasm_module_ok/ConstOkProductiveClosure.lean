import properties.wasm_module_ok.ConstOkForwardClosure
import properties.wasm_module_ok.ConstInstrsProductiveClosure
import properties.wasm_module_ok.ConstDecisionTrace
import properties.wasm_module_ok.ConstFinalPopMatch

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstOkProductiveClosure

/-- Every successful constant expression leaves one produced type in the
finite closure. Its final match to the requested type is kept as a match,
since translated matching may accept `BotT` and subtypes. -/
theorem const_ok_has_productive_matching_output
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype) (xs : SpecTec.const)
    (start finish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Const_ok c t xs⟩)
      start (.success (.of ())) finish) :
    ∃ u : SpecTec.valtype,
      u ∈ FiniteClosure.iterate
        (ConstProductiveClosure.productiveStep c) xs.length ∧
      CandidateValMatch.InTableVal c u ∧
      PopMatchEntries.ValueMatches c u t := by
  obtain ⟨hall, irt, indices, ellipses, middle, hlist, hfinal⟩ :=
    (ConstDecisionTrace.const_ok_decision_trace_iff
      c t xs start finish).1 hconst
  have hresult :=
    ConstInstrsProductiveClosure.instrs_entries_in_productive_closure
      m tr c hc xs hall c [] (irt, indices) 0 start middle
      (ConstStaticAgreement.refl c) hlist
      (by simp) (by simp)
  obtain ⟨hshape, hclosed, htable⟩ := hresult
  rcases irt with ⟨flag, stack⟩
  change flag = .NoEllipses at hshape
  subst flag
  obtain ⟨u, hstack, _⟩ :=
    ConstFinalPopShape.final_const_pop_singleton
      c t stack ellipses middle finish hfinal
  subst stack
  have hmatch :=
    ConstFinalPopMatch.final_const_pop_matches
      c t u ellipses middle finish hfinal
  obtain ⟨before, after, heval⟩ := hmatch
  have hentries :=
    PopMatchEntries.match_resulttype_entries
      c [u] [t] before after heval
  obtain ⟨source, hsource, hrelation⟩ :=
    PopMatchEntries.entries_source c [u] [t]
      hentries t (by simp)
  have hsourceEq : source = u := by simpa using hsource
  subst source
  exact ⟨u, by simpa using hclosed u (by simp),
    htable u (by simp), hrelation⟩

/-- With an explicit target universe and table hypothesis, the final target
belongs to the executable saturation of produced closure types. -/
theorem const_ok_target_in_productive_saturation
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype) (xs : SpecTec.const)
    (start finish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Const_ok c t xs⟩)
      start (.success (.of ())) finish)
    (htarget : t ∈ ConstFieldCandidate.extendedCandidateUniverse c)
    (htable : CandidateValMatch.InTableVal c t) :
    t ∈ ConstExtendedMatchSaturation.extendedMatchSaturation c
      (ConstMatchAwareClosure.sourcesOf c
        (FiniteClosure.iterate
          (ConstProductiveClosure.productiveStep c) xs.length)) := by
  obtain ⟨u, hu, hactual, hmatch⟩ :=
    const_ok_has_productive_matching_output m tr c hc t xs
      start finish hconst
  let s := FiniteClosure.iterate
    (ConstProductiveClosure.productiveStep c) xs.length
  have hbounded : s ⊆ FiniteValidTypes.candidateUniverse c :=
    FiniteClosure.iterate_bounded
      (FiniteValidTypes.candidateUniverse c)
      (ConstProductiveClosure.productiveStep c)
      (ConstProductiveClosure.productive_step_bounded c) xs.length
  have hsource : u ∈ ConstMatchAwareClosure.sourcesOf c s :=
    (ConstMatchAwareClosure.sources_of_mem_iff c s u hbounded).2 hu
  have hbool : CandidateValMatch.candidateValMatch c u t = true :=
    (PopMatchSaturation.value_matches_iff_candidate
      c u t (CandidateTraceReady.trace_ready_at m tr c hc)
      hactual htable).1 hmatch
  exact (ConstExtendedMatchSaturation.extended_match_saturation_mem_iff
    c (ConstMatchAwareClosure.sourcesOf c s) t).2
      ⟨htarget, u, hsource, hbool⟩

/-- The finite candidate universe bounds every successful trace length:
its productive closure is already fixed at the universe cardinality. -/
theorem const_ok_target_in_fixed_productive_saturation
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype) (xs : SpecTec.const)
    (start finish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Const_ok c t xs⟩)
      start (.success (.of ())) finish)
    (htarget : t ∈ ConstFieldCandidate.extendedCandidateUniverse c)
    (htable : CandidateValMatch.InTableVal c t) :
    t ∈ ConstExtendedMatchSaturation.extendedMatchSaturation c
      (ConstMatchAwareClosure.sourcesOf c
        (FiniteClosure.iterate
          (ConstProductiveClosure.productiveStep c)
          (FiniteValidTypes.candidateUniverse c).card)) := by
  let fixed := FiniteClosure.iterate
    (ConstProductiveClosure.productiveStep c)
    (FiniteValidTypes.candidateUniverse c).card
  have hfixed : fixed = ConstProductiveClosure.productiveStep c fixed := by
    exact ConstProductiveClosure.productive_step_fixed_at_card c
  have hclosed : ConstProductiveClosure.productiveStep c fixed ⊆ fixed :=
    Finset.subset_of_eq hfixed.symm
  have hsub : FiniteClosure.iterate
      (ConstProductiveClosure.productiveStep c) xs.length ⊆ fixed :=
    FiniteClosure.iterate_subset_of_closed
      (ConstProductiveClosure.productiveStep c)
      (ConstProductiveClosure.productive_step_mono c)
      fixed hclosed xs.length
  have hbefore := const_ok_target_in_productive_saturation
    m tr c hc t xs start finish hconst htarget htable
  exact ConstExtendedMatchSaturation.extended_match_saturation_mono
    c _ _ (ConstMatchAwareClosure.sources_of_mono c _ _ hsub) hbefore

end properties.wasm_module_ok.ConstOkProductiveClosure
