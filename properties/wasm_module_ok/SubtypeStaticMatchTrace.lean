import properties.wasm_module_ok.CandidateNestedReady
import properties.wasm_module_ok.SubtypeSupertypeShape
import properties.wasm_module_ok.SourceReferenceLookup

set_option autoImplicit false

namespace properties.wasm_module_ok.SubtypeStaticMatchTrace

theorem subtype_sub_ok_static_match_trace
    (c : SpecTec.context) (x y : SpecTec.typeidx)
    (strt : SpecTec.strtype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Subtype_sub_ok' c x strt
        (.VarHT (.StatX y))⟩)
      start (.success (.of ())) finish) :
    ∃ dt : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
    ∃ middle : Nat,
      c.TYPES[y]? = some dt ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.subtype, SpecTec.Call.«$unrolldt» dt⟩)
        start (.success (.of (SpecTec.subtype.SubT fin hts strtU))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_strtype» c.TYPES strt strtU⟩)
        middle (.success (.of true)) finish ∧
      y < x ∧ fin = .NoFinal := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Subtype_sub_ok'_clauses c x strt (.VarHT (.StatX y))))
      start (.success (.of ())) finish at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.tryClauses_success_iff
        (SpecTec.Subtype_sub_ok'_clauses c x strt (.VarHT (.StatX y)))
        start (.of ()) finish).1 hbody
    unfold SpecTec.Subtype_sub_ok'_clauses at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«Subtype_sub_ok':clause:0» at h0
      simp only [SpecTec.«sub:heaptype:heaptypeVar»,
        SpecTec.«Subtype_sub_ok':rule:downcast:0»,
        SpecTec.«exec:match:typevar:StatX»] at h0
      cases h0 with
      | bind_success hguard0 h1 =>
        cases hguard0
        cases h1 with
        | bind_success hguard1 h2 =>
          cases hguard1
          cases h2 with
          | bind_success hguard2 h3 =>
            cases hguard2
            split at h3
            · rename_i lookup dt hlookup
              cases h3 with
              | bind_success hunroll h4 =>
                rename_i middle st
                cases st with
                | SubT fin hts strtU =>
                  dsimp only at h4
                  cases h4 with
                  | bind_success hmatch h5 =>
                    rename_i matchEnd matchResult
                    cases h5 with
                    | bind_success hguard hpure =>
                      cases hpure
                      cases hguard with
                      | guard_true hg =>
                        rcases hg with ⟨⟨hy, hfin⟩, hr⟩
                        subst matchResult
                        exact ⟨dt, fin, hts, strtU, middle,
                          hlookup, hunroll, hmatch, hy, hfin⟩
            · change SpecTecExecution.Eval SpecTec.Body
                .unmatch _ (.success (.of ())) _ at h3
              cases h3
    | next _ hrest =>
      cases hrest

theorem subtype_sub_ok_static_target_indexed
    (c : SpecTec.context) (x y : SpecTec.typeidx)
    (strt : SpecTec.strtype) (start finish : Nat)
    (hready : CandidateNestedReady.nestedTableReady c = true)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Subtype_sub_ok' c x strt
        (.VarHT (.StatX y))⟩)
      start (.success (.of ())) finish) :
    ∃ dt : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
    ∃ middle : Nat,
      c.TYPES[y]? = some dt ∧
      properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
        some (.SubT fin hts strtU) ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_strtype» c.TYPES strt strtU⟩)
        middle (.success (.of true)) finish ∧
      y < x ∧ fin = .NoFinal ∧
      ∀ ht, ht ∈ ReadyMatchReachability.sourceHeaptypes strtU →
        ht ∈ HeaptypeValidation.baseHeaptypes ∨
          ∃ dtK : SpecTec.deftype, ∃ k : Nat,
            ReadyMatchHeaptypeIndex.indexOfDeftype c.TYPES dtK = some k ∧
            ht = .DefHT dtK := by
  obtain ⟨dt, fin, hts, strtU, middle,
      hlookup, hunroll, hmatch, hlt, hfin⟩ :=
    subtype_sub_ok_static_match_trace c x y strt start finish h
  have hbound : y < c.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  obtain ⟨dt', fin', hts', strtU', hget', hresult', hrefs⟩ :=
    CandidateNestedReady.candidate_nested_searchable c y hready hbound
  have hdt : dt' = dt := by
    rw [hlookup] at hget'
    cases hget'
    rfl
  subst dt'
  have hresult :
      properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
        some (.SubT fin hts strtU) :=
    (UnrollInterface.unrolldt_success_iff dt
      (.SubT fin hts strtU) start middle).1 hunroll |>.1
  rw [hresult] at hresult'
  cases hresult'
  exact ⟨dt, fin, hts, strtU, middle,
    hlookup, hresult, hmatch, hlt, hfin, hrefs⟩

theorem static_pair_classes_before_match
    (c : SpecTec.context) (y : SpecTec.typeidx)
    (sourceFin : SpecTec.final) (sourceHts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (dt : SpecTec.deftype)
    (subStart subFinish : Nat)
    (hsub : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_ok c
          (.SubT sourceFin sourceHts strt)⟩)
      subStart (.success (.of ())) subFinish)
    (hready : CandidateNestedReady.nestedTableReady c = true)
    (hlookup : c.TYPES[y]? = some dt) :
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
      properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dt =
        some (.SubT fin hts strtU) ∧
      (∀ ht, ht ∈ ReadyMatchReachability.sourceHeaptypes strt →
        ht ∈ HeaptypeValidation.baseHeaptypes ∨
          ∃ k : Nat, ∃ dtK : SpecTec.deftype,
            c.TYPES[k]? = some dtK ∧ ht = .VarHT (.StatX k)) ∧
      (∀ ht, ht ∈ ReadyMatchReachability.sourceHeaptypes strtU →
        ht ∈ HeaptypeValidation.baseHeaptypes ∨
          ∃ dtK : SpecTec.deftype, ∃ k : Nat,
            ReadyMatchHeaptypeIndex.indexOfDeftype c.TYPES dtK = some k ∧
            ht = .DefHT dtK) := by
  have hy : y < c.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hlookup).1
  obtain ⟨dt', fin, hts, strtU, hlookup', hunroll, htarget⟩ :=
    CandidateNestedReady.candidate_nested_searchable c y hready hy
  have hdt : dt' = dt := by
    rw [hlookup] at hlookup'
    cases hlookup'
    rfl
  subst dt'
  refine ⟨fin, hts, strtU, hunroll, ?_, htarget⟩
  intro ht hmem
  exact SourceReferenceLookup.source_heaptype_base_or_lookup_of_subtype_success
    c sourceFin sourceHts strt ht subStart subFinish hsub hmem

end properties.wasm_module_ok.SubtypeStaticMatchTrace
