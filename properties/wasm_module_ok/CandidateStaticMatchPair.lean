import properties.wasm_module_ok.CandidateRectypeSearch
import properties.wasm_module_ok.SubtypeStaticMatchTrace
import properties.wasm_module_ok.ReadyMatchHeaptypeVar
import properties.wasm_module_ok.SubtypeReadyMatch

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateStaticMatchPair

theorem generated_static_pair_before_match
    (before candidate : SpecTec.context)
    (sts : List SpecTec.subtype) (y : SpecTec.typeidx)
    (sourceFin : SpecTec.final) (sourceHts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (dt : SpecTec.deftype)
    (subStart subFinish : Nat)
    (hgenerated : Gen.support
      (CandidateRectypeSearch.readyGroupGen before) (.RecT sts))
    (hcandidate : CandidateRectypeTable.candidateContext before sts =
      some candidate)
    (hsub : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_ok candidate
          (.SubT sourceFin sourceHts strt)⟩)
      subStart (.success (.of ())) subFinish)
    (hlookup : candidate.TYPES[y]? = some dt) :
    CandidateTypeReady.Ready candidate ∧
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
      properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
        some (.SubT fin hts strtU) ∧
      (∀ ht, ht ∈ ReadyMatchReachability.sourceHeaptypes strt →
        ht ∈ HeaptypeValidation.baseHeaptypes ∨
          ∃ k : Nat, ∃ dtK : SpecTec.deftype,
            candidate.TYPES[k]? = some dtK ∧ ht = .VarHT (.StatX k)) ∧
      (∀ ht, ht ∈ ReadyMatchReachability.sourceHeaptypes strtU →
        ht ∈ HeaptypeValidation.baseHeaptypes ∨
          ∃ dtK : SpecTec.deftype, ∃ k : Nat,
            ReadyMatchHeaptypeIndex.indexOfDeftype candidate.TYPES dtK = some k ∧
            ht = .DefHT dtK) := by
  obtain ⟨candidate', hcontext, hready, hnested⟩ :=
    CandidateRectypeSearch.readyGroupGen_candidate_nested_ready
      before sts hgenerated
  have heq : candidate' = candidate :=
    Option.some.inj (hcontext.symm.trans hcandidate)
  subst candidate'
  exact ⟨hready,
    SubtypeStaticMatchTrace.static_pair_classes_before_match
      candidate y sourceFin sourceHts strt dt subStart subFinish
      hsub hnested hlookup⟩

theorem generated_static_def_match_total
    (before candidate : SpecTec.context)
    (sts : List SpecTec.subtype) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hgenerated : Gen.support
      (CandidateRectypeSearch.readyGroupGen before) (.RecT sts))
    (hcandidate : CandidateRectypeTable.candidateContext before sts =
      some candidate)
    (hP : candidate.TYPES[p]? = some dtP)
    (hQ : candidate.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» candidate.TYPES
        (.VarHT (.StatX p)) (.DefHT dtQ)⟩)
      start (.success (.of
        (ValidatedMatchIndexFuel.matchIndex candidate p q))) start := by
  obtain ⟨candidate', hcontext, hready, _⟩ :=
    CandidateRectypeSearch.readyGroupGen_candidate_nested_ready
      before sts hgenerated
  have heq : candidate' = candidate :=
    Option.some.inj (hcontext.symm.trans hcandidate)
  subst candidate'
  have hp : p < candidate.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hP).1
  have hq : q < candidate.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hQ).1
  exact ReadyMatchHeaptypeVar.ready_match_heaptype_statx_def_total
    candidate p q start dtP dtQ hready hp hq hP hQ

/-- The finite pre-match filter supplies both conditions needed to evaluate
the static supertype check on a selected recursive-group candidate. -/
theorem generated_static_subtype_sub_ok_total
    (before candidate : SpecTec.context)
    (sts : List SpecTec.subtype) (x y : SpecTec.typeidx)
    (sourceFin : SpecTec.final) (sourceHts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (dt : SpecTec.deftype)
    (subStart subFinish n : Nat)
    (hgenerated : Gen.support
      (CandidateRectypeSearch.readyGroupGen before) (.RecT sts))
    (hcandidate : CandidateRectypeTable.candidateContext before sts =
      some candidate)
    (hsub : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_ok candidate
          (.SubT sourceFin sourceHts strt)⟩)
      subStart (.success (.of ())) subFinish)
    (hlookup : candidate.TYPES[y]? = some dt) :
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
    ∃ result : Bool,
      properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
        some (.SubT fin hts strtU) ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.Subtype_sub_ok' candidate x strt
            (.VarHT (.StatX y))⟩)
        n (if (y < x ∧ fin = .NoFinal) ∧ result = true then
          .success (.of ()) else .unmatch) n := by
  obtain ⟨candidate', hcontext, hready, hnested⟩ :=
    CandidateRectypeSearch.readyGroupGen_candidate_nested_ready
      before sts hgenerated
  have heq : candidate' = candidate :=
    Option.some.inj (hcontext.symm.trans hcandidate)
  subst candidate'
  exact SubtypeReadyMatch.static_subtype_sub_ok_total_of_ready
    candidate x y sourceFin sourceHts strt dt subStart subFinish n
    hsub hnested hready hlookup

end properties.wasm_module_ok.CandidateStaticMatchPair
