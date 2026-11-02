import properties.wasm_module_ok.CandidateRectypeConstruction

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidatePairedCompleteness

/-- A successful group passes the exact finite closing check on its computed
candidate context and the actual canonical range. -/
theorem pairedChecks_of_success
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    CandidateGroupSuperChecks.pairedChecks
      result c.TYPES.length (List.range sts.length) sts = true := by
  have hcandidate :=
    CandidateRectypeTable.rectype_success_candidateContext
      c result sts start finish hrect
  have hsource :=
    CandidateSourceChecks.rectype_success_sourceChecks
      c result result sts start finish hrect hcandidate
  have hready : CandidateTypeReady.Ready result :=
    (CandidateTypeReadyDecide.tableReady_true_iff_ready result).mp
      (CandidateTypeReadySuccess.rectype_success_tableReady
        c result sts start finish hc hrect)
  have hnested :=
    CandidateNestedReady.rectype_success_nestedTableReady
      c result sts start finish hc hrect
  obtain ⟨dts, hresult, before, after, hiter⟩ :=
    MatchHeaptypeBasic.rectype_ok_extract_range_and_sub_iter
      c result sts start finish hrect
  have hiterResult : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6»
          result c.TYPES.length (List.range sts.length) sts⟩)
      before (.success (.of ())) after := by
    simpa [hresult] using hiter
  exact ((CandidateGroupSuperChecks.iter6_success_iff_pairedChecks
    result c.TYPES.length (List.range sts.length) sts
    before after hnested hready hsource (by simp)).1 hiterResult).1

end properties.wasm_module_ok.CandidatePairedCompleteness
