import properties.wasm_module_ok.CandidatePairedCompleteness

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateRectypeDecision

/-- Exact finite check for one recursive group in a validated type prefix. -/
def rectypePasses (c : SpecTec.context) (sts : List SpecTec.subtype) : Bool :=
  match CandidateRectypeTable.candidateContext c sts with
  | none => false
  | some candidate =>
      CandidateTypeReadyDecide.tableReady candidate &&
        CandidateNestedReady.nestedTableReady candidate &&
        CandidateSourceChecks.sourceChecks candidate sts &&
        CandidateGroupSuperChecks.pairedChecks
          candidate c.TYPES.length (List.range sts.length) sts

theorem rectypePasses_iff_success
    (c : SpecTec.context) (sts : List SpecTec.subtype) (n : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c) :
    rectypePasses c sts = true ↔
      ∃ result : SpecTec.context,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context,
            SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
          n (.success (.of result)) n := by
  constructor
  · intro hpass
    cases htrans : CandidateRectypeTable.transformed c sts with
    | none =>
        simp [rectypePasses, CandidateRectypeTable.candidateContext,
          htrans] at hpass
    | some rect' =>
        let candidate : SpecTec.context :=
          {c with TYPES := c.TYPES ++
            ((List.range sts.length).map
              (fun i => SpecTec.deftype.DefT rect' i))}
        have hparts :
            (((CandidateTypeReadyDecide.tableReady candidate = true ∧
              CandidateNestedReady.nestedTableReady candidate = true) ∧
              CandidateSourceChecks.sourceChecks candidate sts = true) ∧
              CandidateGroupSuperChecks.pairedChecks
                candidate c.TYPES.length (List.range sts.length) sts = true) := by
          simpa [rectypePasses, CandidateRectypeTable.candidateContext,
            htrans, candidate, Bool.and_eq_true] using hpass
        rcases hparts with ⟨⟨⟨hready, hnested⟩, hsource⟩, hpaired⟩
        refine ⟨candidate, ?_⟩
        exact CandidateRectypeConstruction.rectype_success_of_checks
          c sts rect' n htrans hsource
          ((CandidateTypeReadyDecide.tableReady_true_iff_ready candidate).mp
            hready) hnested hpaired
  · rintro ⟨result, hrect⟩
    have hcontext :=
      CandidateRectypeTable.rectype_success_candidateContext
        c result sts n n hrect
    have hready :=
      CandidateTypeReadySuccess.rectype_success_tableReady
        c result sts n n hc hrect
    have hnested :=
      CandidateNestedReady.rectype_success_nestedTableReady
        c result sts n n hc hrect
    have hsource :=
      CandidateSourceChecks.rectype_success_sourceChecks
        c result result sts n n hrect hcontext
    have hpaired :=
      CandidatePairedCompleteness.pairedChecks_of_success
        c result sts n n hc hrect
    simp [rectypePasses, hcontext, hready, hnested, hsource,
      hpaired]

end properties.wasm_module_ok.CandidateRectypeDecision
