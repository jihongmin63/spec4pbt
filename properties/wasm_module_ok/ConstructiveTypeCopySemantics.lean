import properties.wasm_module_ok.ConstructiveTypeCopy
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopySemantics
open SpecTec
open properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open properties.wasm_module_ok.ConstructiveRelocateIndices properties.wasm_module_ok.ConstructiveTypeCopy

/-- Total structural mapping under an existing source invariant. -/
def mapP {α β : Type} (P : α → Prop) (f : (x : α) → P x → β) :
    (xs : List α) → (∀ x ∈ xs, P x) → List β
  | [], _ => []
  | x::xs, h => f x (h x (by simp)) :: mapP P f xs (fun y hy => h y (by simp [hy]))

@[simp] theorem mapP_length {α β : Type} (P : α → Prop) (f : (x : α) → P x → β)
    (xs : List α) (h : ∀ x ∈ xs, P x) : (mapP P f xs h).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapP,ih]

def indexValue (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (i : Fin (base+width)) : heaptype :=
  if hlocal : base ≤ i.val then .VarHT (.RecX (i.val-base))
  else .DefHT (table[i.val]'(by omega))

theorem index_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (i : Fin (base+width)) :
    closedIndex table base width i.val = some (indexValue table base width hle i) := by
  unfold indexValue
  split
  · exact closedIndex_local table base width i.val ⟨by assumption,i.isLt⟩
  · have hi : i.val < base := by omega
    rw [closedIndex_external table base width i.val hi, List.getElem?_eq_getElem (by omega)]
    rfl

def heapValue (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ht : heaptype) (h : HeapBound (base+width) ht) : heaptype :=
  match ht with
  | .VarHT (.StatX i) => indexValue table base width hle ⟨i,h⟩
  | .VarHT (.RecX _) | .DefHT _ => False.elim h
  | other => other

def refValue (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (rt : reftype) (h : RefBound (base+width) rt) : reftype :=
  match rt with
  | .«% %» nu ht => .«% %» nu (heapValue table base width hle ht h)

def valValue (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (vt : valtype) (h : ValBound (base+width) vt) : valtype :=
  match vt with
  | .RefT rt => .RefT (refValue table base width hle rt h)
  | other => other

def storageValue (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : storagetype) (h : StorageBound (base+width) st) : storagetype :=
  match st with
  | .ValStorageT v => .ValStorageT (valValue table base width hle v h)
  | .PackStorageT p => .PackStorageT p

def fieldValue (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ft : fieldtype) (h : FieldBound (base+width) ft) : fieldtype :=
  match ft with
  | .FieldT mu st => .FieldT mu (storageValue table base width hle st h)

def strValue (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : strtype) (h : StrBound (base+width) st) : strtype :=
  match st with
  | .DefStructT (.StructT fs) => .DefStructT (.StructT
      (mapP (FieldBound (base+width)) (fieldValue table base width hle) fs h))
  | .DefArrayT (.ArrayT f) => .DefArrayT (.ArrayT (fieldValue table base width hle f h))
  | .DefFuncT (.FuncT ins outs) => .DefFuncT (.FuncT
      (mapP (ValBound (base+width)) (valValue table base width hle) ins h.1)
      (mapP (ValBound (base+width)) (valValue table base width hle) outs h.2))

def subValue (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : SpecTec.subtype) (h : SubBound (base+width) st) : SpecTec.subtype :=
  match st with
  | .SubT fin hs st => .SubT fin
      (mapP (HeapBound (base+width)) (heapValue table base width hle) hs h.1)
      (strValue table base width hle st h.2)

def groupValue (table : List deftype) (base : Nat) (hle : base ≤ table.length)
    (sts : List SpecTec.subtype) (h : GroupBound (base+sts.length) sts) : rectype :=
  .RecT (mapP (SubBound (base+sts.length)) (subValue table base sts.length hle) sts h)

theorem heap_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ht : heaptype) (h : HeapBound (base+width) ht) :
    substHeaptypeResult (rollHeaptype ht base (base+width)) table =
      some (heapValue table base width hle ht h) := by
  rcases raw_cases (base+width) ht h with hb | ⟨i,rfl,hi⟩
  · cases ht <;> simp_all [Base,rollHeaptype,substHeaptypeResult,heapValue]
  · exact index_value_correct table base width hle ⟨i,hi⟩

theorem ref_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (rt : reftype) (h : RefBound (base+width) rt) :
    substReftypeResult (rollReftype rt base (base+width)) table =
      some (refValue table base width hle rt h) := by
  rcases rt with ⟨nu,ht⟩
  simp only [rollReftype,substReftypeResult,heap_value_correct table base width hle ht h]
  rfl

theorem val_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (vt : valtype) (h : ValBound (base+width) vt) :
    substValtypeResult (rollValtype vt base (base+width)) table =
      some (valValue table base width hle vt h) := by
  cases vt <;> try rfl
  rename_i rt
  simp only [rollValtype,substValtypeResult,ref_value_correct table base width hle rt h]
  rfl

theorem storage_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : storagetype) (h : StorageBound (base+width) st) :
    substStoragetypeResult (rollStoragetype st base (base+width)) table =
      some (storageValue table base width hle st h) := by
  cases st with
  | PackStorageT p => rfl
  | ValStorageT vt =>
    simp only [rollStoragetype,substStoragetypeResult,val_value_correct table base width hle vt h]
    rfl

theorem field_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ft : fieldtype) (h : FieldBound (base+width) ft) :
    substFieldtypeResult (rollFieldtype ft base (base+width)) table =
      some (fieldValue table base width hle ft h) := by
  rcases ft with ⟨mu,st⟩
  simp only [rollFieldtype,substFieldtypeResult,storage_value_correct table base width hle st h]
  rfl

theorem vals_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (xs : List valtype) (h : ∀ x ∈ xs, ValBound (base+width) x) :
    substResulttypeResult (rollValtypes xs base (base+width)) table =
      some (mapP (ValBound (base+width)) (valValue table base width hle) xs h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [rollValtypes] at ih
    simp only [rollValtypes, List.map_cons, substResulttypeResult]
    rw [val_value_correct table base width hle x (h x (by simp)),
      ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem fields_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (xs : List fieldtype) (h : ∀ x ∈ xs, FieldBound (base+width) x) :
    substFieldtypeListResult (rollFieldtypes xs base (base+width)) table =
      some (mapP (FieldBound (base+width)) (fieldValue table base width hle) xs h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [rollFieldtypes] at ih
    simp only [rollFieldtypes, List.map_cons, substFieldtypeListResult]
    rw [field_value_correct table base width hle x (h x (by simp)),
      ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem heaps_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (xs : List heaptype) (h : ∀ x ∈ xs, HeapBound (base+width) x) :
    substHeaptypeListResult (rollHeaptypes xs base (base+width)) table =
      some (mapP (HeapBound (base+width)) (heapValue table base width hle) xs h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [rollHeaptypes] at ih
    simp only [rollHeaptypes, List.map_cons, substHeaptypeListResult]
    rw [heap_value_correct table base width hle x (h x (by simp)),
      ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem str_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : strtype) (h : StrBound (base+width) st) :
    substStrtypeResult (rollStrtype st base (base+width)) table =
      some (strValue table base width hle st h) := by
  cases st with
  | DefStructT st =>
    cases st with
    | StructT fs =>
      simp only [rollStrtype,rollStructtype,substStrtypeResult,substStructtypeResult,
        fields_value_correct table base width hle fs h]
      rfl
  | DefArrayT ar =>
    cases ar with
    | ArrayT f =>
      simp only [rollStrtype,rollArraytype,substStrtypeResult,substArraytypeResult,
        field_value_correct table base width hle f h]
      rfl
  | DefFuncT ft =>
    cases ft with
    | FuncT ins outs =>
      simp only [rollStrtype,rollFunctype,substStrtypeResult,substFunctypeResult,
        vals_value_correct table base width hle ins h.1,
        vals_value_correct table base width hle outs h.2]
      rfl

theorem sub_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : SpecTec.subtype) (h : SubBound (base+width) st) :
    substSubtypeResult (rollSubtype st base (base+width)) table =
      some (subValue table base width hle st h) := by
  rcases st with ⟨fin,hs,st⟩
  simp only [rollSubtype,substSubtypeResult,
    heaps_value_correct table base width hle hs h.1,
    str_value_correct table base width hle st h.2]
  rfl

theorem subs_value_correct (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (xs : List SpecTec.subtype) (h : ∀ x ∈ xs, SubBound (base+width) x) :
    substSubtypeListResult (rollSubtypes xs base (base+width)) table =
      some (mapP (SubBound (base+width)) (subValue table base width hle) xs h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [rollSubtypes] at ih
    simp only [rollSubtypes, List.map_cons, substSubtypeListResult]
    rw [sub_value_correct table base width hle x (h x (by simp)),
      ih (fun y hy => h y (by simp [hy]))]
    rfl

theorem group_value_correct (table : List deftype) (base : Nat) (hle : base ≤ table.length)
    (sts : List SpecTec.subtype) (h : GroupBound (base+sts.length) sts) :
    substRectypeResult (.RecT (rollSubtypes sts base (base+sts.length))) table =
      some (groupValue table base hle sts h) := by
  simp only [substRectypeResult,subs_value_correct table base sts.length hle sts h]
  rfl

/-- Exact dependent structural traversal, instantiated below for the real
source type syntax. All invariants are proof arguments, never runtime tests. -/
theorem each_exact_value {α β γ : Type} (P : α → Prop) (Q : β → Prop)
    (g : (x : α) → P x → Gen β)
    (old : (x : α) → P x → γ) (new : (y : β) → Q y → γ)
    (hg : ∀ x hx y, Gen.support (g x hx) y ↔ ∃ hy, new y hy = old x hx)
    (xs : List α) (hx : ∀ x ∈ xs, P x) (ys : List β) :
    Gen.support (each P g xs hx) ys ↔
      ∃ hy : ∀ y ∈ ys, Q y, mapP Q new ys hy = mapP P old xs hx := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [each,mapP]
  | cons x xs ih =>
    cases ys with
    | nil => simp [each,mapP]
    | cons y ys =>
      rw [each_support, List.forall₂_cons]
      constructor
      · rintro ⟨⟨hp,hfirst⟩,htail⟩
        obtain ⟨hq,heq⟩ := (hg x hp y).1 hfirst
        obtain ⟨hqs,heqs⟩ := (ih (fun z hz => hx z (by simp [hz])) ys).1
          ((each_support P g xs _ ys).2 htail)
        let hy : ∀ z ∈ y::ys, Q z := by
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact hq
          · exact hqs z hz
        exact ⟨hy, congrArg₂ List.cons heq heqs⟩
      · rintro ⟨hy,he⟩
        have hp := hx x (by simp)
        have hq := hy y (by simp)
        have heq := (List.cons.inj he).1
        have heqs := (List.cons.inj he).2
        refine ⟨⟨hp, (hg x hp y).2 ⟨hq,heq⟩⟩, ?_⟩
        apply (each_support P g xs _ ys).1
        apply (ih _ ys).2
        exact ⟨fun z hz => hy z (by simp [hz]),heqs⟩

theorem heap_exact_value (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ht : heaptype) (h : HeapBound (base+width) ht) (out : heaptype) :
    Gen.support (heap table base width hle ht h) out ↔
      ∃ ho : HeapBound (table.length+width) out,
        heapValue table table.length width (Nat.le_refl _) out ho =
          heapValue table base width hle ht h := by
  rw [heap_exact]
  constructor
  · rintro ⟨ho,he⟩
    rw [heap_value_correct table table.length width (Nat.le_refl _) out ho,
      heap_value_correct table base width hle ht h] at he
    exact ⟨ho,Option.some.inj he⟩
  · rintro ⟨ho,he⟩
    refine ⟨ho,?_⟩
    rw [heap_value_correct table table.length width (Nat.le_refl _) out ho,
      heap_value_correct table base width hle ht h,he]

#print axioms group_value_correct
#print axioms heap_exact_value
end properties.wasm_module_ok.ConstructiveTypeCopySemantics
