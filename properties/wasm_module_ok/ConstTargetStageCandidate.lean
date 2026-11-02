import properties.wasm_module_ok.CandidateTraceReady
import properties.wasm_module_ok.ConstTargetCandidate

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstTargetStageCandidate

/-- A successful constant initializer in an actual module-stage context has
an output candidate that the executable matcher accepts for its target. -/
theorem const_ok_target_candidate_match
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (t : SpecTec.valtype) (ht : t ∈ FiniteValidTypes.candidateUniverse c)
    (xs : SpecTec.const) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      start (.success (.of ())) finish) :
    ∃ u ∈ FiniteValidTypes.candidateUniverse c,
      CandidateValMatch.candidateValMatch c u t = true := by
  obtain ⟨u, hu, before, after, hmatch⟩ :=
    ConstTargetCandidate.const_ok_target_has_candidate_match
      c t xs start finish h
  have hresult :=
    (CandidateTraceReady.trace_candidate_val_match_iff_at
      m tr c hc u t true before after hu ht).mp hmatch
  exact ⟨u, hu, hresult.1.symm⟩

end properties.wasm_module_ok.ConstTargetStageCandidate
