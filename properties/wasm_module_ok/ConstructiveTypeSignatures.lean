import properties.wasm_module_ok.ConstructiveTypeMetadata
import properties.wasm_module_ok.ConstructiveTypeCopyCompatibility

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeSignatures
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ConstructiveTypeCopy ConstructiveTypeCopySemantics ConstructiveTypeEnvironment
open ConstructiveTypeCopyHeapMatch ConstructiveTypeCopyRelations ConstructiveTypeCopyRealization

theorem raw_refl (c : context) (ht : heaptype) (h : HeapBound c.TYPES.length ht) :
    HeapRel c c ht ht := by
  rcases raw_cases _ ht h with hb | ⟨i,rfl,hi⟩
  · have hb' := ConstructiveHeapPlan.base_mem ht hb
    exact ⟨ht,.base ht hb',.base ht hb'⟩
  · exact ⟨.DefHT c.TYPES[i], .stat i c.TYPES[i] (List.getElem?_eq_getElem hi),
      .stat i c.TYPES[i] (List.getElem?_eq_getElem hi)⟩

theorem heap_closed (c : context) (sts : List SpecTec.subtype)
    (h : GroupBound (c.TYPES.length+sts.length) sts) (ht : heaptype)
    (hh : HeapBound (c.TYPES.length+sts.length) ht) :
    HeapRel (extended c sts h) (extended c sts h) ht
      (unrollHeaptype (heapValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) ht hh)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h)) := by
  rcases raw_cases _ ht hh with hb | ⟨i,rfl,hi⟩
  · have hb' := ConstructiveHeapPlan.base_mem ht hb
    have he : unrollHeaptype (heapValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) ht hh)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h) = ht := by
      cases ht <;> simp_all [Base, heapValue, unrollHeaptype]
    rw [he]
    exact ⟨ht,.base ht hb',.base ht hb'⟩
  · obtain ⟨dt,hget,hu⟩ := index_unroll c.TYPES
      (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h) sts.length ⟨i,hi⟩
    change HeapRel _ _ (.VarHT (.StatX i)) (unrollHeaptype
      (indexValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) ⟨i,hh⟩)
      (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h))
    rw [hu]
    exact ⟨.DefHT dt,.stat i dt hget,.closed i dt hget⟩

section Close
variable (c : context) (sts : List SpecTec.subtype)
variable (h : GroupBound (c.TYPES.length+sts.length) sts)

theorem ref_closed (t : reftype) (ht : RefBound (c.TYPES.length+sts.length) t) :
    RefRel (HeapRel (extended c sts h) (extended c sts h)) t
      (unrollReftype (refValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) t ht)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h)) := by
  rcases t with ⟨nu,ht⟩
  exact .mk nu _ _ (heap_closed c sts h _ ht)

theorem val_closed (t : valtype) (ht : ValBound (c.TYPES.length+sts.length) t) :
    ValRel (HeapRel (extended c sts h) (extended c sts h)) t
      (unrollValtype (valValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) t ht)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h)) := by
  cases t with
  | NumT n => exact .num n
  | VecT v => exact .vec v
  | BotT => exact .bot
  | RefT t => exact .ref _ _ (ref_closed c sts h t ht)

theorem storage_closed (t : storagetype) (ht : StorageBound (c.TYPES.length+sts.length) t) :
    StorageRel (HeapRel (extended c sts h) (extended c sts h)) t
      (unrollStoragetype (storageValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) t ht)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h)) := by
  cases t with
  | ValStorageT v => exact .val _ _ (val_closed c sts h v ht)
  | PackStorageT p => exact .pack p

theorem field_closed (t : fieldtype) (ht : FieldBound (c.TYPES.length+sts.length) t) :
    FieldRel (HeapRel (extended c sts h) (extended c sts h)) t
      (unrollFieldtype (fieldValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) t ht)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h)) := by
  rcases t with ⟨mu,s⟩
  exact .mk mu _ _ (storage_closed c sts h s ht)

theorem mapP_map_rel {α β γ : Type} (P : α → Prop)
    (f : (a : α) → P a → β) (g : β → γ) (R : α → γ → Prop)
    (hr : ∀ a ha, R a (g (f a ha))) (xs : List α) (hx : ∀ x ∈ xs, P x) :
    List.Forall₂ R xs ((mapP P f xs hx).map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact .cons (hr x _) (ih _)

theorem str_closed (t : strtype) (ht : StrBound (c.TYPES.length+sts.length) t) :
    StrRel (HeapRel (extended c sts h) (extended c sts h)) t
      (unrollStrtype (strValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) t ht)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h)) := by
  cases t with
  | DefStructT t =>
    cases t
    exact .struct _ _ (mapP_map_rel _ _ _ _ (field_closed c sts h) _ _)
  | DefArrayT t =>
    cases t
    exact .array _ _ (field_closed c sts h _ _)
  | DefFuncT t =>
    cases t
    exact .func _ _ _ _ (mapP_map_rel _ _ _ _ (val_closed c sts h) _ _)
      (mapP_map_rel _ _ _ _ (val_closed c sts h) _ _)
end Close

theorem val_bounds (b : Nat) (v : valtype) (hv : ValBound b v) :
    ∀ ht ∈ ReadyMatchReachability.sourceValHeaptypes v, HeapBound b ht := by
  cases v <;> simp only [ReadyMatchReachability.sourceValHeaptypes, List.not_mem_nil, false_implies, implies_true]
  case RefT t => cases t; simpa [ReadyMatchReachability.sourceValHeaptypes, ValBound, RefBound] using hv

theorem storage_bounds (b : Nat) (s : storagetype) (hs : StorageBound b s) :
    ∀ ht ∈ ReadyMatchReachability.sourceStorageHeaptypes s, HeapBound b ht := by
  cases s with
  | ValStorageT v => exact val_bounds b v hs
  | PackStorageT p => simp [ReadyMatchReachability.sourceStorageHeaptypes]

theorem field_bounds (b : Nat) (f : fieldtype) (hf : FieldBound b f) :
    ∀ ht ∈ ReadyMatchReachability.sourceFieldHeaptypes f, HeapBound b ht := by
  cases f; exact storage_bounds b _ hf

theorem str_bounds (b : Nat) (s : strtype) (hs : StrBound b s) :
    ∀ ht ∈ ReadyMatchReachability.sourceHeaptypes s, HeapBound b ht := by
  cases s with
  | DefStructT s =>
    cases s
    intro ht hm
    obtain ⟨f,hf,hht⟩ := List.mem_flatMap.mp hm
    exact field_bounds b f (hs f hf) ht hht
  | DefArrayT a => cases a; exact field_bounds b _ hs
  | DefFuncT f =>
    cases f
    intro ht hm
    obtain ⟨v,hv,hht⟩ := List.mem_flatMap.mp hm
    rcases List.mem_append.mp hv with hv | hv
    · exact val_bounds b v (hs.1 v hv) ht hht
    · exact val_bounds b v (hs.2 v hv) ht hht

theorem str_raw_refl (c : context) (s : strtype) (hs : StrBound c.TYPES.length s) :
    StrRel (HeapRel c c) s s :=
  ConstructiveTypeCopyCompatibility.str_refl _ s
    (fun ht hm => raw_refl c ht (str_bounds c.TYPES.length s hs ht hm))

/-- Raw source signatures can be retained in generator state. Every subsequent
comparison with the actual unrolled parent has exactly the same meaning. -/
theorem matching (c : context) (hr : CandidateTypeReady.Ready c)
    (source raw closed : strtype) (hs : StrBound c.TYPES.length source)
    (ht : StrRel (HeapRel c c) raw closed) :
    MatchStrtypeConditional.strMatch (fun a b => (ReadyHeapMatch.readyHeapMatch c a b).getD false)
      source closed =
    MatchStrtypeConditional.strMatch (fun a b => (ReadyHeapMatch.readyHeapMatch c a b).getD false)
      source raw := by
  apply str_match (HeapRel c c) _ _ _ source source raw closed (str_raw_refl c source hs) ht
  rintro a a' b b' ⟨av,ha,ha'⟩ ⟨bv,hb,hb'⟩
  rw [normalize c hr a' b' av bv ha' hb', normalize c hr a b av bv ha hb]

end properties.wasm_module_ok.ConstructiveTypeSignatures
