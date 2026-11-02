import properties.wasm_module_ok.ConstructiveTypeCopySemantics

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeClosed
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ConstructiveTypeCopy ConstructiveTypeCopySemantics

/- Closing a bounded raw group replaces every static reference with a local
recursive reference or an existing definition. A second substitution is then
the identity for any target table. These lemmas concern the structural closure;
they do not assume or assert subtype compatibility. -/

theorem index_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (i : Fin (base+width)) :
    substHeaptypeResult (indexValue table base width hle i) target =
      some (indexValue table base width hle i) := by
  unfold indexValue
  split <;> rfl

theorem heap_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (ht : heaptype) (h : HeapBound (base+width) ht) :
    substHeaptypeResult (heapValue table base width hle ht h) target =
      some (heapValue table base width hle ht h) := by
  cases ht <;> try rfl
  case VarHT tv =>
    cases tv with
    | RecX n => exact False.elim h
    | StatX n => exact index_fixed table target base width hle ⟨n,h⟩
  case DefHT dt => exact False.elim h

theorem ref_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (rt : reftype) (h : RefBound (base+width) rt) :
    substReftypeResult (refValue table base width hle rt h) target =
      some (refValue table base width hle rt h) := by
  rcases rt with ⟨nu,ht⟩
  simp only [refValue, substReftypeResult, heap_fixed]
  rfl

theorem val_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (vt : valtype) (h : ValBound (base+width) vt) :
    substValtypeResult (valValue table base width hle vt h) target =
      some (valValue table base width hle vt h) := by
  cases vt <;> try rfl
  case RefT rt =>
    simp only [valValue, substValtypeResult, ref_fixed]
    rfl

theorem storage_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (st : storagetype) (h : StorageBound (base+width) st) :
    substStoragetypeResult (storageValue table base width hle st h) target =
      some (storageValue table base width hle st h) := by
  cases st with
  | PackStorageT p => rfl
  | ValStorageT v =>
    simp only [storageValue, substStoragetypeResult, val_fixed]
    rfl

theorem field_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (ft : fieldtype) (h : FieldBound (base+width) ft) :
    substFieldtypeResult (fieldValue table base width hle ft h) target =
      some (fieldValue table base width hle ft h) := by
  rcases ft with ⟨mu,st⟩
  simp only [fieldValue, substFieldtypeResult, storage_fixed]
  rfl

theorem vals_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (xs : List valtype)
    (h : ∀ x ∈ xs, ValBound (base+width) x) :
    substResulttypeResult (mapP _ (valValue table base width hle) xs h) target =
      some (mapP _ (valValue table base width hle) xs h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapP, substResulttypeResult, val_fixed, ih]
    rfl

theorem fields_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (xs : List fieldtype)
    (h : ∀ x ∈ xs, FieldBound (base+width) x) :
    substFieldtypeListResult (mapP _ (fieldValue table base width hle) xs h) target =
      some (mapP _ (fieldValue table base width hle) xs h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapP, substFieldtypeListResult, field_fixed, ih]
    rfl

theorem heaps_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (xs : List heaptype)
    (h : ∀ x ∈ xs, HeapBound (base+width) x) :
    substHeaptypeListResult (mapP _ (heapValue table base width hle) xs h) target =
      some (mapP _ (heapValue table base width hle) xs h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapP, substHeaptypeListResult, heap_fixed, ih]
    rfl

theorem str_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (st : strtype) (h : StrBound (base+width) st) :
    substStrtypeResult (strValue table base width hle st h) target =
      some (strValue table base width hle st h) := by
  cases st with
  | DefStructT s =>
    cases s
    simp only [strValue, substStrtypeResult, substStructtypeResult, fields_fixed]
    rfl
  | DefArrayT a =>
    cases a
    simp only [strValue, substStrtypeResult, substArraytypeResult, field_fixed]
    rfl
  | DefFuncT f =>
    cases f
    simp only [strValue, substStrtypeResult, substFunctypeResult, vals_fixed]
    rfl

theorem sub_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (st : SpecTec.subtype) (h : SubBound (base+width) st) :
    substSubtypeResult (subValue table base width hle st h) target =
      some (subValue table base width hle st h) := by
  rcases st with ⟨f,ps,st⟩
  simp only [subValue, substSubtypeResult, heaps_fixed, str_fixed]
  rfl

theorem subs_fixed (table target : List deftype) (base width : Nat)
    (hle : base ≤ table.length) (xs : List SpecTec.subtype)
    (h : ∀ x ∈ xs, SubBound (base+width) x) :
    substSubtypeListResult (mapP _ (subValue table base width hle) xs h) target =
      some (mapP _ (subValue table base width hle) xs h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapP, substSubtypeListResult, sub_fixed, ih]
    rfl

theorem group_fixed (table target : List deftype) (base : Nat)
    (hle : base ≤ table.length) (sts : List SpecTec.subtype)
    (h : GroupBound (base+sts.length) sts) :
    substRectypeResult (groupValue table base hle sts h) target =
      some (groupValue table base hle sts h) := by
  simp only [groupValue, substRectypeResult, subs_fixed]
  rfl

theorem definition_fixed (table target : List deftype) (base : Nat)
    (hle : base ≤ table.length) (sts : List SpecTec.subtype)
    (h : GroupBound (base+sts.length) sts) (i : Nat) :
    substDeftypeResult (.DefT (groupValue table base hle sts h) i) target =
      some (.DefT (groupValue table base hle sts h) i) := by
  simp only [substDeftypeResult, group_fixed]
  rfl

end properties.wasm_module_ok.ConstructiveTypeClosed
