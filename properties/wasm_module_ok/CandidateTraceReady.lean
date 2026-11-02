import properties.wasm_module_ok.CandidateProvenanceElemDataFuncs
import properties.wasm_module_ok.LateTypesTransport

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateTraceReady

/-- Every context in the actual module validation trace retains the type table
established by the Types stage. -/
theorem trace_types_eq
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8]) :
    c.TYPES = tr.c0.TYPES := by
  have himports :=
    ((ImportsValidation.imports_success_iff_result
      tr.c0 m.IMPORTS tr.c1 tr.n3 tr.n4).mp tr.imports_ok).1
  have hheaders :=
    ((FuncHeadersStageGenerator.funcs_success_iff_header_result
      tr.c1 m.FUNCS tr.c2 tr.n4 tr.n5).mp tr.funcs_ok).1
  have hmems :=
    ((MemsValidation.mems_success_iff_result
      tr.c3 m.MEMS tr.c4 tr.n6 tr.n7).mp tr.mems_ok).1
  have htags :=
    ((TagsValidation.tags_success_iff_result
      tr.c5 m.TAGS tr.c6 tr.n8 tr.n9).mp tr.tags_ok).1
  have h1 : tr.c1.TYPES = tr.c0.TYPES :=
    ContextTypesValidation.imports_types tr.c0 tr.c1 m.IMPORTS himports
  have h2 : tr.c2.TYPES = tr.c0.TYPES :=
    (ContextTypesValidation.headers_types tr.c1 tr.c2
      (m.FUNCS.map (·.FTYPE)) hheaders).trans h1
  have h3 : tr.c3.TYPES = tr.c0.TYPES :=
    (DeclarationTypesValidation.tables_ok_types
      tr.c2 tr.c3 m.TABLES tr.n5 tr.n6 tr.tables_ok).trans h2
  have h4 : tr.c4.TYPES = tr.c0.TYPES :=
    (ContextTypesValidation.mems_types tr.c3 tr.c4 m.MEMS hmems).trans h3
  have h5 : tr.c5.TYPES = tr.c0.TYPES :=
    (DeclarationTypesValidation.globals_ok_types
      tr.c4 tr.c5 m.GLOBALS tr.n7 tr.n8 tr.globals_ok).trans h4
  have h6 : tr.c6.TYPES = tr.c0.TYPES :=
    (ContextTypesValidation.tags_types tr.c5 tr.c6 m.TAGS htags).trans h5
  have h7 : tr.c7.TYPES = tr.c0.TYPES :=
    (DeclarationTypesValidation.elems_ok_types
      tr.c6 tr.c7 m.ELEMS tr.n9 tr.n10 tr.elems_ok).trans h6
  have h8 : tr.c8.TYPES = tr.c0.TYPES :=
    (DeclarationTypesValidation.datas_ok_types
      tr.c7 tr.c8 m.DATAS tr.n10 tr.n11 tr.datas_ok).trans h7
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with h | h | h | h | h | h | h | h | h
  · subst c; rfl
  · subst c; exact h1
  · subst c; exact h2
  · subst c; exact h3
  · subst c; exact h4
  · subst c; exact h5
  · subst c; exact h6
  · subst c; exact h7
  · subst c; exact h8

theorem trace_ready_at
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8]) :
    CandidateTypeReady.Ready c := by
  have hvalidated : ValidatedTypeChain.ValidatedTypes tr.c0 :=
    ValidatedTypeChain.types_ok_preserves
      {tr.c with REFS := tr.free} tr.c0 m.TYPES tr.n2 tr.n3
      (CandidateTypesTraceIntegration.initial_validated m tr) tr.types_ok
  exact CandidateProvenanceElemDataFuncs.ready_of_types_eq tr.c0 c
    (trace_types_eq m tr c hc)
    (CandidateTypeReady.validated_types_ready tr.c0 hvalidated)

theorem trace_provenance_at
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8]) :
    CandidateUniverseReady.Provenance c := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with h | h | h | h | h | h | h | h | h
  · subst c; exact CandidateProvenanceSeed.trace_types_provenance m tr
  · subst c; exact CandidateProvenanceSeed.trace_imports_provenance m tr
  · subst c; exact CandidateProvenanceSeed.trace_funcs_provenance m tr
  · subst c; exact CandidateProvenancePreGlobals.trace_tables_provenance m tr
  · subst c; exact CandidateProvenancePreGlobals.trace_mems_provenance m tr
  · subst c; exact CandidateProvenancePostGlobals.trace_globals_provenance m tr
  · subst c; exact CandidateProvenancePostGlobals.trace_tags_provenance m tr
  · subst c; exact CandidateProvenanceElemDataFuncs.trace_elems_provenance m tr
  · subst c; exact CandidateProvenanceElemDataFuncs.trace_datas_provenance m tr

theorem trace_candidate_val_match_iff_at
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (u t : SpecTec.valtype) (b : Bool) (start finish : Nat)
    (hu : u ∈ FiniteValidTypes.candidateUniverse c)
    (ht : t ∈ FiniteValidTypes.candidateUniverse c) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» c.TYPES u t⟩)
      start (.success (.of b)) finish ↔
    b = CandidateValMatch.candidateValMatch c u t ∧ finish = start := by
  exact CandidateUniverseReady.candidate_universe_match_iff
    c u t b start finish
    (trace_ready_at m tr c hc)
    (trace_provenance_at m tr c hc) hu ht

end properties.wasm_module_ok.CandidateTraceReady
