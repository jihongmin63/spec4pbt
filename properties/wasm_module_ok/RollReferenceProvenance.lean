import properties.wasm_module_ok.SubstReferenceProvenance

set_option autoImplicit false

namespace properties.wasm_module_ok.RollReferenceProvenance

open properties.wasm_module_not_ok.Rejection
open properties.wasm_module_ok.ReadyMatchReachability

theorem source_val_roll
    (t : SpecTec.valtype) (x y : Nat) :
    sourceValHeaptypes (rollValtype t x y) =
      (sourceValHeaptypes t).map (fun ht => rollHeaptype ht x y) := by
  cases t with
  | NumT _ => rfl
  | VecT _ => rfl
  | BotT => rfl
  | RefT rt => cases rt <;> rfl

theorem source_storage_roll
    (st : SpecTec.storagetype) (x y : Nat) :
    sourceStorageHeaptypes (rollStoragetype st x y) =
      (sourceStorageHeaptypes st).map (fun ht => rollHeaptype ht x y) := by
  cases st with
  | ValStorageT t => exact source_val_roll t x y
  | PackStorageT _ => rfl

theorem source_field_roll
    (ft : SpecTec.fieldtype) (x y : Nat) :
    sourceFieldHeaptypes (rollFieldtype ft x y) =
      (sourceFieldHeaptypes ft).map (fun ht => rollHeaptype ht x y) := by
  cases ft with
  | FieldT _ st => exact source_storage_roll st x y

private theorem source_val_list_roll
    (ts : List SpecTec.valtype) (x y : Nat) :
    (rollValtypes ts x y).flatMap sourceValHeaptypes =
      (ts.flatMap sourceValHeaptypes).map
        (fun ht => rollHeaptype ht x y) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [rollValtypes] at ih
      simp [rollValtypes, source_val_roll, ih, List.map_append]

private theorem source_field_list_roll
    (fields : List SpecTec.fieldtype) (x y : Nat) :
    (rollFieldtypes fields x y).flatMap sourceFieldHeaptypes =
      (fields.flatMap sourceFieldHeaptypes).map
        (fun ht => rollHeaptype ht x y) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      simp only [rollFieldtypes] at ih
      simp [rollFieldtypes, source_field_roll, ih, List.map_append]

theorem source_heaptypes_roll
    (strt : SpecTec.strtype) (x y : Nat) :
    sourceHeaptypes (rollStrtype strt x y) =
      (sourceHeaptypes strt).map (fun ht => rollHeaptype ht x y) := by
  cases strt with
  | DefStructT st =>
      cases st with
      | StructT fields =>
          simpa [sourceHeaptypes, rollStrtype, rollStructtype] using
            source_field_list_roll fields x y
  | DefArrayT arr =>
      cases arr with
      | ArrayT field =>
          simpa [sourceHeaptypes, rollStrtype, rollArraytype] using
            source_field_roll field x y
  | DefFuncT ft =>
      cases ft with
      | FuncT inputs outputs =>
          simpa [sourceHeaptypes, rollStrtype, rollFunctype,
            rollValtypes, List.map_append] using
            source_val_list_roll (inputs ++ outputs) x y

theorem source_heaptype_mem_roll_iff
    (strt : SpecTec.strtype) (x y : Nat)
    (rolled : SpecTec.heaptype) :
    rolled ∈ sourceHeaptypes (rollStrtype strt x y) ↔
      ∃ ht, ht ∈ sourceHeaptypes strt ∧
        rollHeaptype ht x y = rolled := by
  rw [source_heaptypes_roll]
  simp only [List.mem_map]

theorem rectype_ok_appended_source_reference
    (before after : SpecTec.context)
    (sts sts' : List SpecTec.subtype)
    (start finish i : Nat)
    (dts : List SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hafter : after = {before with TYPES := before.TYPES ++ dts})
    (hdts : dts[i]? = some (.DefT (.RecT sts') i)) :
    ∃ hts' : List SpecTec.heaptype,
    ∃ strt' : SpecTec.strtype,
      sts'[i]? = some (.SubT fin hts' strt') ∧
      ∀ raw, raw ∈ sourceHeaptypes strt' →
        ∃ ht, ht ∈ sourceHeaptypes strt ∧
          substHeaptypeResult
            (rollHeaptype ht before.TYPES.length
              (sts.length + before.TYPES.length))
            before.TYPES = some raw := by
  obtain ⟨hts', strt', hget, hpredecessor⟩ :=
    SubstReferenceProvenance.rectype_ok_appended_reference_predecessor
      before after sts sts' start finish i dts fin hts strt
      hrect hi hsource hafter hdts
  refine ⟨hts', strt', hget, ?_⟩
  intro raw hmem
  obtain ⟨rolled, hrolledMem, hsubst⟩ := hpredecessor raw hmem
  obtain ⟨ht, hsourceMem, hroll⟩ :=
    (source_heaptype_mem_roll_iff strt before.TYPES.length
      (sts.length + before.TYPES.length) rolled).1 hrolledMem
  subst rolled
  exact ⟨ht, hsourceMem, hsubst⟩

end properties.wasm_module_ok.RollReferenceProvenance
