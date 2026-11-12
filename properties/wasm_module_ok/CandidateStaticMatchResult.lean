import properties.wasm_module_ok.CandidateStaticMatchPair
import properties.wasm_module_ok.ReadyStaticSubtypeMatch

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateStaticMatchResult

/-- The pre-match candidate filter makes the translated closing static
supertype check executable with the exact Boolean from the safe classifier. -/
theorem generated_static_subtype_sub_ok_result
    (before candidate : SpecTec.context)
    (sts : List SpecTec.subtype) (x y : SpecTec.typeidx)
    (sourceFin : SpecTec.final) (sourceHts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (dt : SpecTec.deftype)
    (subStart subFinish n : Nat)
    (hgenerated : Gen.support
      (CandidateRectypeSearch.readyGroupGen before) (.RecT sts))
    (hcandidate : CandidateRectypeTable.candidateContext before sts =
      some candidate)
    (hsub : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_ok candidate
          (.SubT sourceFin sourceHts strt)⟩)
      subStart (.success (.of ())) subFinish)
    (hlookup : candidate.TYPES[y]? = some dt) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_sub_ok' candidate x strt
          (.VarHT (.StatX y))⟩)
      n (if ReadyStaticSubtypeMatch.staticSuperMatch candidate x y strt dt = true then
        .success (.of ()) else .unmatch) n := by
  obtain ⟨candidate', hcontext, hready, hnested⟩ :=
    CandidateRectypeSearch.readyGroupGen_candidate_nested_ready
      before sts hgenerated
  have heq : candidate' = candidate :=
    Option.some.inj (hcontext.symm.trans hcandidate)
  subst candidate'
  exact ReadyStaticSubtypeMatch.static_subtype_sub_ok_result_of_ready
    candidate x y sourceFin sourceHts strt dt
    subStart subFinish n hsub hnested hready hlookup

end properties.wasm_module_ok.CandidateStaticMatchResult
