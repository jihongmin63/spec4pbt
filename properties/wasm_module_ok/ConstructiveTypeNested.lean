import properties.wasm_module_ok.ConstructiveTypeSignatures

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeNested
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ConstructiveTypeCopy ConstructiveTypeCopySemantics ConstructiveTypeEnvironment
open ConstructiveTypeCopyHeapMatch

section Closed
variable (c : context) (sts : List SpecTec.subtype)
variable (h : GroupBound (c.TYPES.length+sts.length) sts)

theorem heap_canonical (ht : heaptype) (hh : HeapBound (c.TYPES.length+sts.length) ht) :
    Canonical (extended c sts h)
      (unrollHeaptype (heapValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) ht hh)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h)) := by
  rcases raw_cases _ ht hh with hb | ⟨i,rfl,hi⟩
  · left
    have hb' := ConstructiveHeapPlan.base_mem ht hb
    cases ht <;> simp_all [Base,heapValue,unrollHeaptype]
  · obtain ⟨dt,hget,hu⟩ := index_unroll c.TYPES
      (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h) sts.length ⟨i,hi⟩
    change Canonical _ (unrollHeaptype
      (indexValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) ⟨i,hh⟩) _)
    rw [hu]
    exact Or.inr ⟨i,dt,hget,rfl⟩

theorem val_canonical (v : valtype) (hv : ValBound (c.TYPES.length+sts.length) v) :
    ∀ ht ∈ ReadyMatchReachability.sourceValHeaptypes
      (unrollValtype (valValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) v hv)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h)), Canonical (extended c sts h) ht := by
  cases v <;> try simp [valValue,unrollValtype,ReadyMatchReachability.sourceValHeaptypes]
  case RefT rt =>
    rcases rt with ⟨nu,ht⟩
    simpa [valValue,refValue,unrollValtype,unrollReftype,ReadyMatchReachability.sourceValHeaptypes] using
      heap_canonical c sts h ht hv

theorem storage_canonical (s : storagetype) (hs : StorageBound (c.TYPES.length+sts.length) s) :
    ∀ ht ∈ ReadyMatchReachability.sourceStorageHeaptypes
      (unrollStoragetype (storageValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) s hs)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h)), Canonical (extended c sts h) ht := by
  cases s with
  | ValStorageT v => exact val_canonical c sts h v hs
  | PackStorageT p => simp [storageValue,unrollStoragetype,ReadyMatchReachability.sourceStorageHeaptypes]

theorem field_canonical (f : fieldtype) (hf : FieldBound (c.TYPES.length+sts.length) f) :
    ∀ ht ∈ ReadyMatchReachability.sourceFieldHeaptypes
      (unrollFieldtype (fieldValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) f hf)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h)), Canonical (extended c sts h) ht := by
  cases f; exact storage_canonical c sts h _ hf

theorem mapP_all {α β γ : Type} (P : α → Prop) (f : (x : α) → P x → β)
    (g : β → γ) (Q : γ → Prop) (hq : ∀ x hx, Q (g (f x hx)))
    (xs : List α) (hx : ∀ x ∈ xs, P x) :
    ∀ y ∈ (mapP P f xs hx).map g, Q y := by
  induction xs with
  | nil => simp [mapP]
  | cons x xs ih => simpa [mapP] using And.intro (hq x _) (ih _)

theorem str_canonical (s : strtype) (hs : StrBound (c.TYPES.length+sts.length) s) :
    ∀ ht ∈ ReadyMatchReachability.sourceHeaptypes
      (unrollStrtype (strValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) s hs)
        (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h)), Canonical (extended c sts h) ht := by
  cases s with
  | DefStructT s =>
    rcases s with ⟨fs⟩
    intro ht hm
    obtain ⟨f,hf,hht⟩ := List.mem_flatMap.mp hm
    exact mapP_all _ _ _
      (fun f => ∀ ht ∈ ReadyMatchReachability.sourceFieldHeaptypes f, Canonical (extended c sts h) ht)
      (field_canonical c sts h) fs hs f hf ht hht
  | DefArrayT a => cases a; exact field_canonical c sts h _ hs
  | DefFuncT f =>
    rcases f with ⟨ins,outs⟩
    intro ht hm
    obtain ⟨v,hv,hht⟩ := List.mem_flatMap.mp hm
    rcases List.mem_append.mp hv with hv | hv
    · exact mapP_all _ _ _
        (fun v => ∀ ht ∈ ReadyMatchReachability.sourceValHeaptypes v, Canonical (extended c sts h) ht)
        (val_canonical c sts h) ins hs.1 v hv ht hht
    · exact mapP_all _ _ _
        (fun v => ∀ ht ∈ ReadyMatchReachability.sourceValHeaptypes v, Canonical (extended c sts h) ht)
        (val_canonical c sts h) outs hs.2 v hv ht hht
end Closed

/-- Every stored signature's nested references remain searchable after closing
a bounded raw group. This is derived structurally before subtype matching. -/
theorem nested (c : context) (sts : List SpecTec.subtype)
    (h : GroupBound (c.TYPES.length+sts.length) sts)
    (hc : CandidateNestedReady.nestedTableReady c = true) :
    CandidateNestedReady.nestedTableReady (extended c sts h) = true := by
  apply (CandidateNestedReady.nestedTableReady_true_iff _).2
  intro p hp
  by_cases hold : p < c.TYPES.length
  · obtain ⟨dt,f,ps,st,hget,hu,hrefs⟩ :=
      (CandidateNestedReady.nestedTableReady_true_iff c).1 hc p hold
    refine ⟨dt,f,ps,st,?_,hu,?_⟩
    · simpa [extended,List.getElem?_append_left hold] using hget
    · intro ht hm
      rcases hrefs ht hm with hb | ⟨k,dtK,hk,rfl⟩
      · exact Or.inl hb
      · refine Or.inr ⟨k,dtK,?_,rfl⟩
        simpa [extended,List.getElem?_append_left (List.getElem?_eq_some_iff.mp hk).1] using hk
  · have hi : p-c.TYPES.length < sts.length := by
      simp only [extended,List.length_append,definitions,List.length_map,List.length_range] at hp
      omega
    have hpos : c.TYPES.length+(p-c.TYPES.length) = p := Nat.add_sub_cancel' (by omega)
    have hg := List.getElem?_eq_getElem hi
    cases he : sts[p-c.TYPES.length] with
    | SubT f ps st =>
      rw [he] at hg
      have hs := h _ (List.mem_of_getElem? hg)
      let rt := groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h
      refine ⟨.DefT rt (p-c.TYPES.length),f,
        unrollHeaptypes (mapP _ (heapValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _)) ps hs.1) rt,
        unrollStrtype (strValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) st hs.2) rt,
        ?_,?_,?_⟩
      · have hx := definition_lookup c.TYPES rt sts.length (p-c.TYPES.length) hi
        simpa [extended,rt,hpos] using hx
      · exact group_unroll c.TYPES sts h (p-c.TYPES.length) f ps st hg hs
      · exact str_canonical c sts h st hs.2

end properties.wasm_module_ok.ConstructiveTypeNested
