import properties.wasm_module_ok.CandidateProvenanceImports
import properties.wasm_module_ok.CandidateTypesTraceIntegration
import properties.wasm_module_ok.TypeGlobalsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateProvenanceSeed

theorem empty_context_funcs_nil
    (out : SpecTec.context) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.«$empty_context»⟩)
      start (.success (.of out)) finish) :
    out.FUNCS = [] := by
  cases h with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$empty_context_clauses»))
        start (.success (.of out)) finish at hbody
      cases hbody with
      | orElse_success hclause =>
          unfold SpecTec.«$empty_context:clause:0» at hclause
          cases hclause with
          | bind_success _ hpure =>
              cases hpure with
              | pure => rfl
      | orElse_unmatch _ hnone => cases hnone

theorem candidate_context_funcs
    (c out : SpecTec.context) (sts : List SpecTec.subtype)
    (h : CandidateRectypeTable.candidateContext c sts = some out) :
    out.FUNCS = c.FUNCS := by
  cases htrans : CandidateRectypeTable.transformed c sts with
  | none =>
      simp [CandidateRectypeTable.candidateContext, htrans] at h
  | some rect =>
      simp [CandidateRectypeTable.candidateContext, htrans] at h
      cases h
      rfl

theorem types_result_funcs
    (c out : SpecTec.context) (ts : List SpecTec.type)
    (h : CandidateTypesDecision.typesResult c ts = some out) :
    out.FUNCS = c.FUNCS := by
  induction ts generalizing c out with
  | nil =>
      simp [CandidateTypesDecision.typesResult] at h
      cases h
      rfl
  | cons t ts ih =>
      cases t with
      | RecT sts =>
          by_cases hpass : CandidateRectypeDecision.rectypePasses c sts = true
          · cases hcontext : CandidateRectypeTable.candidateContext c sts with
            | none =>
                simp [CandidateTypesDecision.typesResult, hpass, hcontext] at h
            | some next =>
                have htail : CandidateTypesDecision.typesResult next ts =
                    some out := by
                  simpa [CandidateTypesDecision.typesResult, hpass,
                    hcontext] using h
                exact (ih next out htail).trans
                  (candidate_context_funcs c next sts hcontext)
          · simp [CandidateTypesDecision.typesResult, hpass] at h

theorem trace_types_provenance
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    CandidateUniverseReady.Provenance tr.c0 := by
  have hfuncSeed := empty_context_funcs_nil
    tr.c tr.n1 tr.n2 tr.empty_ok
  have hglobSeed := ConstCandidateBot.empty_context_globals_nil
    tr.c tr.n1 tr.n2 tr.empty_ok
  have hresult := CandidateTypesDecision.types_result_of_success
    {tr.c with REFS := tr.free} tr.c0 m.TYPES
    tr.n2 tr.n3 (CandidateTypesTraceIntegration.initial_validated m tr)
    tr.types_ok
  have hfuncOut := types_result_funcs _ tr.c0 m.TYPES hresult
  have hglobOut := TypeGlobalsValidation.types_ok_globals
    {tr.c with REFS := tr.free} tr.c0 m.TYPES
    tr.n2 tr.n3 tr.types_ok
  exact CandidateProvenanceSteps.empty_fields tr.c0
    (by simpa [hfuncSeed] using hfuncOut)
    (by simpa [hglobSeed] using hglobOut)

theorem trace_imports_provenance
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    CandidateUniverseReady.Provenance tr.c1 := by
  exact CandidateProvenanceImports.imports_ok_provenance
    tr.c0 tr.c1 m.IMPORTS tr.n3 tr.n4
    (trace_types_provenance m tr) tr.imports_ok

theorem trace_funcs_provenance
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    CandidateUniverseReady.Provenance tr.c2 := by
  have hresult :=
    ((FuncsValidation.funcs_success_iff_result
      tr.c1 m.FUNCS tr.c2 tr.n4 tr.n5).mp tr.funcs_ok).1
  exact CandidateProvenanceSteps.funcs_result_provenance
    tr.c1 tr.c2 m.FUNCS (trace_imports_provenance m tr) hresult

end properties.wasm_module_ok.CandidateProvenanceSeed
