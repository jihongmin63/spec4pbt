import properties.wasm_module_ok.CandidateRolledSubstBridge
import properties.wasm_module_ok.CandidateRangeExact
import properties.wasm_module_ok.CandidateSourceChecks
import properties.wasm_module_ok.CandidateGroupSuperChecks

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateRectypeConstruction

open properties.wasm_module_not_ok.Rejection

/-- Construct the actual ordered recursive-group call from its computed
candidate table and the two finite validation passes. -/
theorem rectype_success_of_checks
    (c : SpecTec.context) (sts : List SpecTec.subtype)
    (rect' : SpecTec.rectype) (n : Nat)
    (htrans : CandidateRectypeTable.transformed c sts = some rect')
    (hsource : CandidateSourceChecks.sourceChecks
      {c with TYPES := c.TYPES ++
        (List.range sts.length).map (fun i => SpecTec.deftype.DefT rect' i)}
      sts = true)
    (hready : CandidateTypeReady.Ready
      {c with TYPES := c.TYPES ++
        (List.range sts.length).map (fun i => SpecTec.deftype.DefT rect' i)})
    (hnested : CandidateNestedReady.nestedTableReady
      {c with TYPES := c.TYPES ++
        (List.range sts.length).map (fun i => SpecTec.deftype.DefT rect' i)} = true)
    (hpaired : CandidateGroupSuperChecks.pairedChecks
      {c with TYPES := c.TYPES ++
        (List.range sts.length).map (fun i => SpecTec.deftype.DefT rect' i)}
      c.TYPES.length (List.range sts.length) sts = true) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      n (.success (.of
        {c with TYPES := c.TYPES ++
          (List.range sts.length).map (fun i => SpecTec.deftype.DefT rect' i)})) n := by
  let dts : List SpecTec.deftype :=
    (List.range sts.length).map (fun i => SpecTec.deftype.DefT rect' i)
  let candidate : SpecTec.context := {c with TYPES := c.TYPES ++ dts}
  have hsubstValue : CandidateSubstList.substList c
      (rollDeftypes c.TYPES.length (.RecT sts)) = some dts := by
    simpa [dts, htrans] using
      (CandidateRolledSubstBridge.subst_rolled_exact c sts)
  have hsubst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.deftype,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:2» c
          (rollDeftypes c.TYPES.length (.RecT sts))⟩)
      n (.success (.of dts)) n := by
    simpa [hsubstValue, optionOutcome] using
      (CandidateSubstList.subst_list_total c
        (rollDeftypes c.TYPES.length (.RecT sts)) n)
  have hiter5 : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» candidate sts⟩)
      n (.success (.of ())) n :=
    (CandidateSourceChecks.iter5_success_iff_sourceChecks
      candidate sts n n).2 ⟨hsource, rfl⟩
  have hiter6 : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6»
          candidate c.TYPES.length (List.range sts.length) sts⟩)
      n (.success (.of ())) n :=
    (CandidateGroupSuperChecks.iter6_success_iff_pairedChecks
      candidate c.TYPES.length (List.range sts.length) sts n n
      hnested hready hsource (by simp)).2 ⟨hpaired, rfl⟩
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.Rectype_ok_clauses c (.RecT sts)) ())
    n (.success (.of candidate)) n
  apply SpecTecExecution.firstSuccess_cons_success
  unfold SpecTec.«Rectype_ok:clause:0»
  apply SpecTecExecution.Eval.bind_success
    (properties.wasm_module_ok.MatchHeaptypeBasic.range_total sts.length n)
  apply SpecTecExecution.Eval.bind_success
    (rolldt_total c.TYPES.length (.RecT sts) n)
  apply SpecTecExecution.Eval.bind_success hsubst
  apply SpecTecExecution.Eval.bind_success hiter5
  apply SpecTecExecution.Eval.bind_success
    (SpecTecExecution.Eval.guard_true (by simp))
  apply SpecTecExecution.Eval.bind_success hiter6
  exact SpecTecExecution.Eval.pure candidate

end properties.wasm_module_ok.CandidateRectypeConstruction
