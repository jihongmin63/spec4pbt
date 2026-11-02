import properties.wasm_module_ok.CandidateRectypeDecision
import properties.wasm_module_ok.CandidateTypesTrace

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateRectypeStep

/-- The finite group check also recognizes a successful call whose original
execution used arbitrary supply endpoints. -/
theorem passes_of_success
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    CandidateRectypeDecision.rectypePasses c sts = true ∧
      CandidateRectypeTable.candidateContext c sts = some result := by
  have hcontext :=
    CandidateRectypeTable.rectype_success_candidateContext
      c result sts start finish hrect
  have hready :=
    CandidateTypeReadySuccess.rectype_success_tableReady
      c result sts start finish hc hrect
  have hnested :=
    CandidateNestedReady.rectype_success_nestedTableReady
      c result sts start finish hc hrect
  have hsource :=
    CandidateSourceChecks.rectype_success_sourceChecks
      c result result sts start finish hrect hcontext
  have hpaired :=
    CandidatePairedCompleteness.pairedChecks_of_success
      c result sts start finish hc hrect
  exact ⟨by simp [CandidateRectypeDecision.rectypePasses, hcontext,
    hready, hnested, hsource, hpaired], hcontext⟩

/-- A passing group produces precisely the context computed before its
closing checks. -/
theorem success_of_passes
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (n : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hpass : CandidateRectypeDecision.rectypePasses c sts = true)
    (hcontext : CandidateRectypeTable.candidateContext c sts = some result) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      n (.success (.of result)) n := by
  obtain ⟨result', hrect⟩ :=
    (CandidateRectypeDecision.rectypePasses_iff_success c sts n hc).mp hpass
  have hcontext' :=
    CandidateRectypeTable.rectype_success_candidateContext
      c result' sts n n hrect
  have : result' = result := Option.some.inj (hcontext'.symm.trans hcontext)
  subst result'
  exact hrect

end properties.wasm_module_ok.CandidateRectypeStep
