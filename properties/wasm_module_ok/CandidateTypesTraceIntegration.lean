import properties.wasm_module_ok.CandidateTypesStateStage

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateTypesTraceIntegration

theorem empty_context_types_nil
    (out : SpecTec.context) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$empty_context»⟩)
      start (.success (.of out)) finish) :
    out.TYPES = [] := by
  cases h with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$empty_context_clauses») ())
        start (.success (.of out)) finish at hbody
      cases hbody with
      | orElse_success hclause =>
          unfold SpecTec.«$empty_context:clause:0» at hclause
          cases hclause with
          | bind_success _ hpure =>
              cases hpure with
              | pure => rfl
      | orElse_unmatch _ hnone => cases hnone

theorem initial_validated
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    ValidatedTypeChain.ValidatedTypes
      {tr.c with REFS := tr.free} := by
  apply ValidatedTypeChain.ValidatedTypes.seed
  simpa using empty_context_types_nil
    tr.c tr.n1 tr.n2 tr.empty_ok

theorem types_of_trace
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    Gen.support (CandidateTypesStateStage.typesStateGen
      {tr.c with REFS := tr.free}) (m.TYPES, tr.c0) := by
  apply (CandidateTypesStateStage.typesState_support_iff
    {tr.c with REFS := tr.free} m.TYPES tr.c0).2
  exact CandidateTypesDecision.types_result_of_success
    {tr.c with REFS := tr.free} tr.c0 m.TYPES
    tr.n2 tr.n3 (initial_validated m tr) tr.types_ok

theorem types_state_iff_call
    (c out : SpecTec.context) (ts : List SpecTec.type)
    (n : Nat) (hc : ValidatedTypeChain.ValidatedTypes c) :
    Gen.support (CandidateTypesStateStage.typesStateGen c) (ts, out) ↔
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Types_ok c ts⟩)
        n (.success (.of out)) n := by
  exact (CandidateTypesStateStage.typesState_support_iff c ts out).trans
    (CandidateTypesDecision.types_result_iff_success
      c out ts n hc)

end properties.wasm_module_ok.CandidateTypesTraceIntegration
