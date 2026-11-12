import properties.wasm_module_ok.RollReferenceProvenance
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeSourceValidation

theorem rectype_ok_extract_validation_iter
    (before after : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish) :
    ∃ dts : List SpecTec.deftype,
      after = {before with TYPES := before.TYPES ++ dts} ∧
      ∃ iterStart iterFinish : Nat,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Unit,
            SpecTec.Call.«Rectype_ok:rule:iter:5»
              {before with TYPES := before.TYPES ++ dts} sts⟩)
          iterStart (.success (.of ())) iterFinish := by
  cases hrect with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Rectype_ok_clauses before (.RecT sts)))
        start (.success (.of after)) finish at hbody
      obtain ⟨idx, hselected⟩ :=
        (properties.wasm_module_ok.Execution.tryClauses_success_iff
          (SpecTec.Rectype_ok_clauses before (.RecT sts))
          start (.of after) finish).1 hbody
      unfold SpecTec.Rectype_ok_clauses at hselected
      cases hselected with
      | here h0 =>
          unfold SpecTec.«Rectype_ok:clause:0» at h0
          dsimp only at h0
          cases h0 with
          | bind_success _ h1 =>
              dsimp only at h1
              cases h1 with
              | bind_success _ h2 =>
                  dsimp only at h2
                  cases h2 with
                  | bind_success hsubst h3 =>
                      rename_i dts
                      dsimp only at h3
                      cases h3 with
                      | bind_success hiter5 h4 =>
                          dsimp only at h4
                          cases h4 with
                          | bind_success _ h5 =>
                              dsimp only at h5
                              cases h5 with
                              | bind_success _ h6 =>
                                  rename_i v
                                  cases h6
                                  cases v
                                  exact ⟨dts, rfl, _, _, hiter5⟩
      | next _ hrest => cases hrest

theorem validation_iter_member
    (c : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hiter : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Rectype_ok:rule:iter:5» c sts⟩)
      start (.success (.of ())) finish) :
    ∀ st, st ∈ sts →
      ∃ subStart subFinish : Nat,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Unit, SpecTec.Call.Subtype_ok c st⟩)
          subStart (.success (.of ())) subFinish := by
  induction sts generalizing start finish with
  | nil =>
      intro st hmem
      cases hmem
  | cons head tail ih =>
      cases hiter with
      | call hbody =>
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.«Rectype_ok:rule:iter:5_clauses» c (head :: tail)))
            start (.success (.of ())) finish at hbody
          obtain ⟨idx, hselected⟩ :=
            (properties.wasm_module_ok.Execution.tryClauses_success_iff
              (SpecTec.«Rectype_ok:rule:iter:5_clauses» c (head :: tail))
              start (.of ()) finish).1 hbody
          unfold SpecTec.«Rectype_ok:rule:iter:5_clauses» at hselected
          cases hselected with
          | here h0 =>
              unfold SpecTec.«Rectype_ok:rule:iter:5:clause:0» at h0
              cases h0
          | next _ hrest =>
              cases hrest with
              | here h1 =>
                  unfold SpecTec.«Rectype_ok:rule:iter:5:clause:1» at h1
                  cases h1 with
                  | bind_success hhead htailplan =>
                      cases htailplan with
                      | bind_success htail _ =>
                          intro st hmem
                          rcases List.mem_cons.mp hmem with heq | htailmem
                          · subst st
                            exact ⟨_, _, hhead⟩
                          · exact ih _ _ htail st htailmem
              | next _ hrest => cases hrest

theorem rectype_ok_source_strtype_valid
    (before after : SpecTec.context)
    (sts : List SpecTec.subtype)
    (start finish i : Nat)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt)) :
    StrtypeValidation.strtypeValid after strt = true := by
  obtain ⟨dts, hafter, iterStart, iterFinish, hiter⟩ :=
    rectype_ok_extract_validation_iter before after sts start finish hrect
  have hsourceEq : sts[i] = .SubT fin hts strt := by
    have hget : sts[i]? = some sts[i] := List.getElem?_eq_getElem hi
    exact Option.some.inj (hget.symm.trans hsource)
  have hmem : .SubT fin hts strt ∈ sts := by
    simpa [hsourceEq] using (List.getElem_mem hi)
  obtain ⟨subStart, subFinish, hsub⟩ :=
    validation_iter_member
      {before with TYPES := before.TYPES ++ dts}
      sts iterStart iterFinish hiter (.SubT fin hts strt) hmem
  have hvalid :=
    ReadyMatchReachability.source_strtype_valid_of_subtype_success
      {before with TYPES := before.TYPES ++ dts}
      fin hts strt subStart subFinish hsub
  simpa [hafter] using hvalid

theorem rectype_ok_source_heaptype_base_or_stat
    (before after : SpecTec.context)
    (sts : List SpecTec.subtype)
    (start finish i : Nat)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (ht : SpecTec.heaptype)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hmem : ht ∈ ReadyMatchReachability.sourceHeaptypes strt) :
    ht ∈ HeaptypeValidation.baseHeaptypes ∨
      ∃ x : Nat, ht = .VarHT (.StatX x) ∧ x < after.TYPES.length :=
  ReadyMatchReachability.source_heaptype_base_or_stat
    after strt ht
    (rectype_ok_source_strtype_valid
      before after sts start finish i fin hts strt hrect hi hsource)
    hmem

theorem rectype_ok_types_length
    (before after : SpecTec.context)
    (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish) :
    after.TYPES.length = before.TYPES.length + sts.length := by
  obtain ⟨dts, hafter, hlen⟩ :=
    RectypeLengthValidation.rectype_ok_appended_types_length
      before after sts start finish hrect
  rw [hafter, List.length_append, hlen]

end properties.wasm_module_ok.RectypeSourceValidation
