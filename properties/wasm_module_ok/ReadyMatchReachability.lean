import properties.wasm_module_ok.SubtypeValidation
import properties.wasm_module_ok.ReadyMatchHeaptypeVar

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyMatchReachability

open properties.wasm_module_not_ok.Rejection

def sourceValHeaptypes : SpecTec.valtype → List SpecTec.heaptype
  | .RefT (.«% %» _ ht) => [ht]
  | _ => []

def sourceStorageHeaptypes : SpecTec.storagetype → List SpecTec.heaptype
  | .ValStorageT t => sourceValHeaptypes t
  | .PackStorageT _ => []

def sourceFieldHeaptypes : SpecTec.fieldtype → List SpecTec.heaptype
  | .FieldT _ st => sourceStorageHeaptypes st

def sourceHeaptypes : SpecTec.strtype → List SpecTec.heaptype
  | .DefStructT (.StructT fields) => fields.flatMap sourceFieldHeaptypes
  | .DefArrayT (.ArrayT field) => sourceFieldHeaptypes field
  | .DefFuncT (.FuncT inputs outputs) =>
      (inputs ++ outputs).flatMap sourceValHeaptypes

theorem source_val_unroll
    (t : SpecTec.valtype) (rect : SpecTec.rectype) :
    sourceValHeaptypes (unrollValtype t rect) =
      (sourceValHeaptypes t).map (fun ht => unrollHeaptype ht rect) := by
  cases t with
  | NumT _ => rfl
  | VecT _ => rfl
  | BotT => rfl
  | RefT rt => cases rt <;> rfl

theorem source_storage_unroll
    (st : SpecTec.storagetype) (rect : SpecTec.rectype) :
    sourceStorageHeaptypes (unrollStoragetype st rect) =
      (sourceStorageHeaptypes st).map (fun ht => unrollHeaptype ht rect) := by
  cases st with
  | ValStorageT t => exact source_val_unroll t rect
  | PackStorageT _ => rfl

theorem source_field_unroll
    (ft : SpecTec.fieldtype) (rect : SpecTec.rectype) :
    sourceFieldHeaptypes (unrollFieldtype ft rect) =
      (sourceFieldHeaptypes ft).map (fun ht => unrollHeaptype ht rect) := by
  cases ft with
  | FieldT _ st => exact source_storage_unroll st rect

private theorem source_val_list_unroll
    (ts : List SpecTec.valtype) (rect : SpecTec.rectype) :
    (unrollValtypes ts rect).flatMap sourceValHeaptypes =
      (ts.flatMap sourceValHeaptypes).map
        (fun ht => unrollHeaptype ht rect) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [unrollValtypes] at ih
      simp [unrollValtypes, source_val_unroll, ih, List.map_append]

private theorem source_field_list_unroll
    (fields : List SpecTec.fieldtype) (rect : SpecTec.rectype) :
    (unrollFieldtypes fields rect).flatMap sourceFieldHeaptypes =
      (fields.flatMap sourceFieldHeaptypes).map
        (fun ht => unrollHeaptype ht rect) := by
  induction fields with
  | nil => rfl
  | cons field fields ih =>
      simp only [unrollFieldtypes] at ih
      simp [unrollFieldtypes, source_field_unroll, ih, List.map_append]

theorem source_heaptypes_unroll
    (strt : SpecTec.strtype) (rect : SpecTec.rectype) :
    sourceHeaptypes (unrollStrtype strt rect) =
      (sourceHeaptypes strt).map (fun ht => unrollHeaptype ht rect) := by
  cases strt with
  | DefStructT st =>
      cases st with
      | StructT fields =>
          simpa [sourceHeaptypes, unrollStrtype, unrollStructtype] using
            source_field_list_unroll fields rect
  | DefArrayT arr =>
      cases arr with
      | ArrayT field =>
          simpa [sourceHeaptypes, unrollStrtype, unrollArraytype] using
            source_field_unroll field rect
  | DefFuncT ft =>
      cases ft with
      | FuncT inputs outputs =>
          simpa [sourceHeaptypes, unrollStrtype, unrollFunctype,
            unrollValtypes, List.map_append] using
            source_val_list_unroll (inputs ++ outputs) rect

theorem source_heaptype_mem_unroll_iff
    (strt : SpecTec.strtype) (rect : SpecTec.rectype)
    (ht : SpecTec.heaptype) :
    ht ∈ sourceHeaptypes (unrollStrtype strt rect) ↔
      ∃ raw, raw ∈ sourceHeaptypes strt ∧
        unrollHeaptype raw rect = ht := by
  rw [source_heaptypes_unroll]
  simp only [List.mem_map]

private theorem source_val_heaptype_valid
    (c : SpecTec.context) (t : SpecTec.valtype)
    (ht : SpecTec.heaptype)
    (hvalid : ValtypeValidation.valtypeValid c t = true)
    (hmem : ht ∈ sourceValHeaptypes t) :
    HeaptypeValidation.heaptypeValid c ht = true := by
  cases t with
  | NumT _ => simp [sourceValHeaptypes] at hmem
  | VecT _ => simp [sourceValHeaptypes] at hmem
  | BotT => simp [sourceValHeaptypes] at hmem
  | RefT rt =>
      cases rt with
      | «% %» _ refht =>
          simp only [sourceValHeaptypes, List.mem_singleton] at hmem
          subst ht
          simpa [ValtypeValidation.valtypeValid] using hvalid

private theorem source_storage_heaptype_valid
    (c : SpecTec.context) (st : SpecTec.storagetype)
    (ht : SpecTec.heaptype)
    (hvalid : StoragetypeValidation.storagetypeValid c st = true)
    (hmem : ht ∈ sourceStorageHeaptypes st) :
    HeaptypeValidation.heaptypeValid c ht = true := by
  cases st with
  | ValStorageT t =>
      exact source_val_heaptype_valid c t ht hvalid hmem
  | PackStorageT _ => simp [sourceStorageHeaptypes] at hmem

private theorem source_field_heaptype_valid
    (c : SpecTec.context) (ft : SpecTec.fieldtype)
    (ht : SpecTec.heaptype)
    (hvalid : FieldtypeValidation.fieldtypeValid c ft = true)
    (hmem : ht ∈ sourceFieldHeaptypes ft) :
    HeaptypeValidation.heaptypeValid c ht = true := by
  cases ft with
  | FieldT _ st =>
      exact source_storage_heaptype_valid c st ht hvalid hmem

private theorem source_val_list_heaptype_valid
    (c : SpecTec.context) (ts : List SpecTec.valtype)
    (ht : SpecTec.heaptype)
    (hvalid : ResulttypeListValidation.allValtypesValid c ts = true)
    (hmem : ht ∈ ts.flatMap sourceValHeaptypes) :
    HeaptypeValidation.heaptypeValid c ht = true := by
  induction ts with
  | nil => simp at hmem
  | cons t ts ih =>
      have hparts :
          ValtypeValidation.valtypeValid c t = true ∧
          ResulttypeListValidation.allValtypesValid c ts = true := by
        simpa [ResulttypeListValidation.allValtypesValid, Bool.and_eq_true] using hvalid
      have hsplit :
          ht ∈ sourceValHeaptypes t ∨ ht ∈ ts.flatMap sourceValHeaptypes := by
        simpa using hmem
      rcases hsplit with hhead | htail
      · exact source_val_heaptype_valid c t ht hparts.1 hhead
      · exact ih hparts.2 htail

private theorem source_field_list_heaptype_valid
    (c : SpecTec.context) (fields : List SpecTec.fieldtype)
    (ht : SpecTec.heaptype)
    (hvalid : StructtypeFieldListValidation.allFieldsValid c fields = true)
    (hmem : ht ∈ fields.flatMap sourceFieldHeaptypes) :
    HeaptypeValidation.heaptypeValid c ht = true := by
  induction fields with
  | nil => simp at hmem
  | cons field fields ih =>
      have hparts :
          FieldtypeValidation.fieldtypeValid c field = true ∧
          StructtypeFieldListValidation.allFieldsValid c fields = true := by
        simpa [StructtypeFieldListValidation.allFieldsValid, Bool.and_eq_true] using hvalid
      have hsplit :
          ht ∈ sourceFieldHeaptypes field ∨
            ht ∈ fields.flatMap sourceFieldHeaptypes := by
        simpa using hmem
      rcases hsplit with hhead | htail
      · exact source_field_heaptype_valid c field ht hparts.1 hhead
      · exact ih hparts.2 htail

theorem source_heaptype_valid
    (c : SpecTec.context) (strt : SpecTec.strtype)
    (ht : SpecTec.heaptype)
    (hvalid : StrtypeValidation.strtypeValid c strt = true)
    (hmem : ht ∈ sourceHeaptypes strt) :
    HeaptypeValidation.heaptypeValid c ht = true := by
  cases strt with
  | DefStructT st =>
      cases st with
      | StructT fields =>
          exact source_field_list_heaptype_valid c fields ht
            (by simpa [StrtypeValidation.strtypeValid,
                StructArrayValidation.structtypeValid] using hvalid)
            (by simpa [sourceHeaptypes] using hmem)
  | DefArrayT arr =>
      cases arr with
      | ArrayT field =>
          exact source_field_heaptype_valid c field ht
            (by simpa [StrtypeValidation.strtypeValid,
                StructArrayValidation.arraytypeValid] using hvalid)
            (by simpa [sourceHeaptypes] using hmem)
  | DefFuncT ft =>
      cases ft with
      | FuncT inputs outputs =>
          have hparts :
              ResulttypeListValidation.allValtypesValid c inputs = true ∧
              ResulttypeListValidation.allValtypesValid c outputs = true := by
            simpa [StrtypeValidation.strtypeValid,
              FunctypeValidation.functypeValid,
              FunctypeValidation.resulttypeValid,
              Bool.and_eq_true] using hvalid
          have hsplit :
              ht ∈ inputs.flatMap sourceValHeaptypes ∨
                ht ∈ outputs.flatMap sourceValHeaptypes := by
            simpa [sourceHeaptypes, List.flatMap_append] using hmem
          rcases hsplit with hin | hout
          · exact source_val_list_heaptype_valid c inputs ht hparts.1 hin
          · exact source_val_list_heaptype_valid c outputs ht hparts.2 hout

theorem source_heaptype_base_or_stat
    (c : SpecTec.context) (strt : SpecTec.strtype)
    (ht : SpecTec.heaptype)
    (hvalid : StrtypeValidation.strtypeValid c strt = true)
    (hmem : ht ∈ sourceHeaptypes strt) :
    ht ∈ HeaptypeValidation.baseHeaptypes ∨
      ∃ x : Nat, ht = .VarHT (.StatX x) ∧ x < c.TYPES.length :=
  (HeaptypeValidation.heaptype_valid_iff c ht).1
    (source_heaptype_valid c strt ht hvalid hmem)

theorem source_strtype_valid_of_subtype_success
    (c : SpecTec.context) (fin : SpecTec.final)
    (hts : List SpecTec.heaptype) (strt : SpecTec.strtype)
    (start finish : Nat)
    (hsub : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_ok c (.SubT fin hts strt)⟩)
      start (.success (.of ())) finish) :
    StrtypeValidation.strtypeValid c strt = true := by
  have hvalid :=
    (SubtypeValidation.subtype_success_iff_valid
      c (.SubT fin hts strt) start finish).1 hsub
  simp only [SubtypeValidation.subtypeValid, Bool.and_eq_true] at hvalid
  exact hvalid.1.2

theorem source_heaptype_base_or_stat_of_subtype_success
    (c : SpecTec.context) (fin : SpecTec.final)
    (hts : List SpecTec.heaptype) (strt : SpecTec.strtype)
    (ht : SpecTec.heaptype) (start finish : Nat)
    (hsub : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_ok c (.SubT fin hts strt)⟩)
      start (.success (.of ())) finish)
    (hmem : ht ∈ sourceHeaptypes strt) :
    ht ∈ HeaptypeValidation.baseHeaptypes ∨
      ∃ x : Nat, ht = .VarHT (.StatX x) ∧ x < c.TYPES.length :=
  source_heaptype_base_or_stat c strt ht
    (source_strtype_valid_of_subtype_success c fin hts strt start finish hsub)
    hmem

end properties.wasm_module_ok.ReadyMatchReachability
