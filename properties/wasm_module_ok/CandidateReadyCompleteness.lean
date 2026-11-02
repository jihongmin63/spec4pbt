import properties.wasm_module_ok.CandidateTypeReady
import properties.wasm_module_ok.CandidateRectypeTable

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateReadyCompleteness

theorem rectype_success_candidate_ready
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    ∃ candidate,
      CandidateRectypeTable.candidateContext c sts = some candidate ∧
      CandidateTypeReady.Ready candidate := by
  exact ⟨result,
    CandidateRectypeTable.rectype_success_candidateContext
      c result sts start finish hrect,
    CandidateTypeReady.validated_types_ready result
      (ValidatedTypeChain.ValidatedTypes.append
        c result sts start finish hc hrect)⟩

end properties.wasm_module_ok.CandidateReadyCompleteness
