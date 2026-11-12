import properties.wasm_module_ok.ReadyMatchReachability
import properties.wasm_module_ok.ValidatedStrtypeSubstitution

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstReferenceProvenance

open properties.wasm_module_not_ok.Rejection
open properties.wasm_module_ok.ReadyMatchReachability

theorem val_reference_predecessor
    (t t' : SpecTec.valtype) (dts : List SpecTec.deftype)
    (ht' : SpecTec.heaptype)
    (hsubst : substValtypeResult t dts = some t')
    (hmem : ht' ∈ sourceValHeaptypes t') :
    ∃ ht, ht ∈ sourceValHeaptypes t ∧
      substHeaptypeResult ht dts = some ht' := by
  cases t with
  | NumT nt =>
      have heq : t' = .NumT nt := by
        simpa [substValtypeResult] using hsubst.symm
      subst t'
      simp [sourceValHeaptypes] at hmem
  | VecT vt =>
      have heq : t' = .VecT vt := by
        simpa [substValtypeResult] using hsubst.symm
      subst t'
      simp [sourceValHeaptypes] at hmem
  | BotT =>
      have heq : t' = .BotT := by
        simpa [substValtypeResult] using hsubst.symm
      subst t'
      simp [sourceValHeaptypes] at hmem
  | RefT rt =>
      cases rt with
      | «% %» null raw =>
          cases hheap : substHeaptypeResult raw dts with
          | none =>
              simp [substValtypeResult, substReftypeResult, hheap] at hsubst
          | some output =>
              have heq : t' = .RefT (.«% %» null output) := by
                simpa [substValtypeResult, substReftypeResult, hheap]
                  using hsubst.symm
              subst t'
              simp only [sourceValHeaptypes, List.mem_singleton] at hmem
              subst ht'
              exact ⟨raw, by simp [sourceValHeaptypes], hheap⟩

theorem storage_reference_predecessor
    (st st' : SpecTec.storagetype) (dts : List SpecTec.deftype)
    (ht' : SpecTec.heaptype)
    (hsubst : substStoragetypeResult st dts = some st')
    (hmem : ht' ∈ sourceStorageHeaptypes st') :
    ∃ ht, ht ∈ sourceStorageHeaptypes st ∧
      substHeaptypeResult ht dts = some ht' := by
  cases st with
  | PackStorageT pt =>
      have heq : st' = .PackStorageT pt := by
        simpa [substStoragetypeResult] using hsubst.symm
      subst st'
      simp [sourceStorageHeaptypes] at hmem
  | ValStorageT t =>
      cases hval : substValtypeResult t dts with
      | none => simp [substStoragetypeResult, hval] at hsubst
      | some t' =>
          have heq : st' = .ValStorageT t' := by
            simpa [substStoragetypeResult, hval] using hsubst.symm
          subst st'
          exact val_reference_predecessor t t' dts ht' hval hmem

theorem field_reference_predecessor
    (ft ft' : SpecTec.fieldtype) (dts : List SpecTec.deftype)
    (ht' : SpecTec.heaptype)
    (hsubst : substFieldtypeResult ft dts = some ft')
    (hmem : ht' ∈ sourceFieldHeaptypes ft') :
    ∃ ht, ht ∈ sourceFieldHeaptypes ft ∧
      substHeaptypeResult ht dts = some ht' := by
  cases ft with
  | FieldT mu st =>
      cases hstorage : substStoragetypeResult st dts with
      | none => simp [substFieldtypeResult, hstorage] at hsubst
      | some st' =>
          have heq : ft' = .FieldT mu st' := by
            simpa [substFieldtypeResult, hstorage] using hsubst.symm
          subst ft'
          exact storage_reference_predecessor st st' dts ht' hstorage hmem

theorem val_list_reference_predecessor
    (ts ts' : List SpecTec.valtype) (dts : List SpecTec.deftype)
    (ht' : SpecTec.heaptype)
    (hsubst : substResulttypeResult ts dts = some ts')
    (hmem : ht' ∈ ts'.flatMap sourceValHeaptypes) :
    ∃ ht, ht ∈ ts.flatMap sourceValHeaptypes ∧
      substHeaptypeResult ht dts = some ht' := by
  induction ts generalizing ts' with
  | nil =>
      have heq : ts' = [] := by
        simpa [substResulttypeResult] using hsubst.symm
      subst ts'
      simp at hmem
  | cons t ts ih =>
      cases hhead : substValtypeResult t dts with
      | none => simp [substResulttypeResult, hhead] at hsubst
      | some t' =>
          cases htail : substResulttypeResult ts dts with
          | none => simp [substResulttypeResult, hhead, htail] at hsubst
          | some rest' =>
              have heq : ts' = t' :: rest' := by
                simpa [substResulttypeResult, hhead, htail] using hsubst.symm
              subst ts'
              have hsplit :
                  ht' ∈ sourceValHeaptypes t' ∨
                    ht' ∈ rest'.flatMap sourceValHeaptypes := by
                simpa using hmem
              rcases hsplit with hfirst | hrest
              · obtain ⟨ht, hsrc, hmap⟩ :=
                  val_reference_predecessor t t' dts ht' hhead hfirst
                exact ⟨ht, by simpa using Or.inl hsrc, hmap⟩
              · obtain ⟨ht, hsrc, hmap⟩ := ih rest' htail hrest
                exact ⟨ht, by simpa using Or.inr hsrc, hmap⟩

theorem field_list_reference_predecessor
    (fields fields' : List SpecTec.fieldtype)
    (dts : List SpecTec.deftype) (ht' : SpecTec.heaptype)
    (hsubst : substFieldtypeListResult fields dts = some fields')
    (hmem : ht' ∈ fields'.flatMap sourceFieldHeaptypes) :
    ∃ ht, ht ∈ fields.flatMap sourceFieldHeaptypes ∧
      substHeaptypeResult ht dts = some ht' := by
  induction fields generalizing fields' with
  | nil =>
      have heq : fields' = [] := by
        simpa [substFieldtypeListResult] using hsubst.symm
      subst fields'
      simp at hmem
  | cons field fields ih =>
      cases hhead : substFieldtypeResult field dts with
      | none => simp [substFieldtypeListResult, hhead] at hsubst
      | some field' =>
          cases htail : substFieldtypeListResult fields dts with
          | none => simp [substFieldtypeListResult, hhead, htail] at hsubst
          | some rest' =>
              have heq : fields' = field' :: rest' := by
                simpa [substFieldtypeListResult, hhead, htail]
                  using hsubst.symm
              subst fields'
              have hsplit :
                  ht' ∈ sourceFieldHeaptypes field' ∨
                    ht' ∈ rest'.flatMap sourceFieldHeaptypes := by
                simpa using hmem
              rcases hsplit with hfirst | hrest
              · obtain ⟨ht, hsrc, hmap⟩ :=
                  field_reference_predecessor field field' dts ht' hhead hfirst
                exact ⟨ht, by simpa using Or.inl hsrc, hmap⟩
              · obtain ⟨ht, hsrc, hmap⟩ := ih rest' htail hrest
                exact ⟨ht, by simpa using Or.inr hsrc, hmap⟩

theorem strtype_reference_predecessor
    (st st' : SpecTec.strtype) (dts : List SpecTec.deftype)
    (ht' : SpecTec.heaptype)
    (hsubst : substStrtypeResult st dts = some st')
    (hmem : ht' ∈ sourceHeaptypes st') :
    ∃ ht, ht ∈ sourceHeaptypes st ∧
      substHeaptypeResult ht dts = some ht' := by
  cases st with
  | DefStructT struct =>
      cases struct with
      | StructT fields =>
          cases hfields : substFieldtypeListResult fields dts with
          | none =>
              simp [substStrtypeResult, substStructtypeResult, hfields] at hsubst
          | some fields' =>
              have heq : st' = .DefStructT (.StructT fields') := by
                simpa [substStrtypeResult, substStructtypeResult, hfields]
                  using hsubst.symm
              subst st'
              exact field_list_reference_predecessor
                fields fields' dts ht' hfields hmem
  | DefArrayT arr =>
      cases arr with
      | ArrayT field =>
          cases hfield : substFieldtypeResult field dts with
          | none =>
              simp [substStrtypeResult, substArraytypeResult, hfield] at hsubst
          | some field' =>
              have heq : st' = .DefArrayT (.ArrayT field') := by
                simpa [substStrtypeResult, substArraytypeResult, hfield]
                  using hsubst.symm
              subst st'
              exact field_reference_predecessor
                field field' dts ht' hfield hmem
  | DefFuncT ft =>
      cases ft with
      | FuncT inputs outputs =>
          cases hinputs : substResulttypeResult inputs dts with
          | none =>
              simp [substStrtypeResult, substFunctypeResult, hinputs] at hsubst
          | some inputs' =>
              cases houtputs : substResulttypeResult outputs dts with
              | none =>
                  simp [substStrtypeResult, substFunctypeResult,
                    hinputs, houtputs] at hsubst
              | some outputs' =>
                  have heq : st' = .DefFuncT (.FuncT inputs' outputs') := by
                    simpa [substStrtypeResult, substFunctypeResult,
                      hinputs, houtputs] using hsubst.symm
                  subst st'
                  have hsplit :
                      ht' ∈ inputs'.flatMap sourceValHeaptypes ∨
                        ht' ∈ outputs'.flatMap sourceValHeaptypes := by
                    simpa [sourceHeaptypes, List.flatMap_append] using hmem
                  rcases hsplit with hfirst | hsecond
                  · obtain ⟨ht, hsrc, hmap⟩ :=
                      val_list_reference_predecessor
                        inputs inputs' dts ht' hinputs hfirst
                    exact ⟨ht,
                      by simpa [sourceHeaptypes, List.flatMap_append]
                        using Or.inl hsrc,
                      hmap⟩
                  · obtain ⟨ht, hsrc, hmap⟩ :=
                      val_list_reference_predecessor
                        outputs outputs' dts ht' houtputs hsecond
                    exact ⟨ht,
                      by simpa [sourceHeaptypes, List.flatMap_append]
                        using Or.inr hsrc,
                      hmap⟩

theorem rectype_ok_appended_reference_predecessor
    (before after : SpecTec.context)
    (sts sts' : List SpecTec.subtype)
    (start finish i : Nat)
    (dts : List SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hafter : after = {before with TYPES := before.TYPES ++ dts})
    (hdts : dts[i]? = some (.DefT (.RecT sts') i)) :
    ∃ hts' : List SpecTec.heaptype,
    ∃ strt' : SpecTec.strtype,
      sts'[i]? = some (.SubT fin hts' strt') ∧
      ∀ raw, raw ∈ sourceHeaptypes strt' →
        ∃ rolled,
          rolled ∈ sourceHeaptypes
            (rollStrtype strt before.TYPES.length
              (sts.length + before.TYPES.length)) ∧
          substHeaptypeResult rolled before.TYPES = some raw := by
  obtain ⟨hts', strt', hget, hsubst⟩ :=
    ValidatedStrtypeSubstitution.rectype_ok_appended_strtype_subst
      before after sts sts' start finish i dts fin hts strt
      hrect hi hsource hafter hdts
  refine ⟨hts', strt', hget, ?_⟩
  intro raw hmem
  exact strtype_reference_predecessor
    (rollStrtype strt before.TYPES.length
      (sts.length + before.TYPES.length))
    strt' before.TYPES raw hsubst hmem

end properties.wasm_module_ok.SubstReferenceProvenance
