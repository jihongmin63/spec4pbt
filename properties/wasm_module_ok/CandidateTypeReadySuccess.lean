import properties.wasm_module_ok.CandidateTypeReadyDecide

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateTypeReadySuccess

/-- Successful recursive-group validation implies that the pure finite
pre-match restriction accepts the resulting type table. This direction is
used for completeness; it does not authorize running a matcher on an
unvalidated candidate. -/
theorem rectype_success_tableReady
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    CandidateTypeReadyDecide.tableReady result = true := by
  apply (CandidateTypeReadyDecide.tableReady_true_iff_ready result).2
  exact CandidateTypeReady.validated_types_ready result
    (ValidatedTypeChain.ValidatedTypes.append
      c result sts start finish hc hrect)

end properties.wasm_module_ok.CandidateTypeReadySuccess
