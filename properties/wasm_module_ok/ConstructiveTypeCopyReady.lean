import properties.wasm_module_ok.ConstructiveTypeCopySource
import properties.wasm_module_ok.CandidateTypeReadyExtension
import properties.wasm_module_ok.CandidateNestedReady
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopyReady
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection

/-- Appending existing closed definitions requires no new validation premise.
Every predecessor witness can be reused from the old table. -/
theorem ready_duplicates (c : context) (ds : List deftype)
    (hr : CandidateTypeReady.Ready c) (hd : ∀ dt ∈ ds, dt ∈ c.TYPES) :
    CandidateTypeReady.Ready {c with TYPES := c.TYPES++ds} := by
  apply CandidateTypeReadyExtension.ready_append c ds hr
  · intro p dt hp he
    have hm : dt ∈ ds := by
      have hget : ds[p-c.TYPES.length]? = some dt := by
        simpa [List.getElem?_append_right hp] using he
      exact List.mem_iff_getElem?.2 ⟨_,hget⟩
    obtain ⟨k,hk⟩ := List.mem_iff_getElem?.1 (hd dt hm)
    exact SubstPrefixDeftype.substDeftypeResult_prefix dt c.TYPES ds dt (hr.substitution k dt hk)
  · intro p hp hbound
    let dt := (c.TYPES++ds)[p]'hbound
    have he : (c.TYPES++ds)[p]? = some dt := List.getElem?_eq_getElem hbound
    have hm : dt ∈ ds := by
      have hget : ds[p-c.TYPES.length]? = some dt := by
        simpa [List.getElem?_append_right hp] using he
      exact List.mem_iff_getElem?.2 ⟨_,hget⟩
    obtain ⟨k,hk⟩ := List.mem_iff_getElem?.1 (hd dt hm)
    have hkb : k<c.TYPES.length := (List.getElem?_eq_some_iff.1 hk).1
    obtain ⟨dt',fin,hs,st,hk',hu,hedges⟩ := hr.unrolledPredecessors k hkb
    have hdt : dt'=dt := Option.some.inj (hk'.symm.trans hk)
    subst dt'
    refine ⟨dt,fin,hs,st,he,hu,?_⟩
    intro j hj
    obtain ⟨q,dq,hqk,hq,hh⟩ := hedges j hj
    refine ⟨q,dq,by omega,?_,hh⟩
    simpa [List.getElem?_append_left (by omega : q<c.TYPES.length)] using hq

/-- Nested closed references are preserved by the same duplicate extension. -/
theorem nested_duplicates (c : context) (ds : List deftype)
    (hn : CandidateNestedReady.nestedTableReady c = true)
    (hd : ∀ dt ∈ ds, dt ∈ c.TYPES) :
    CandidateNestedReady.nestedTableReady {c with TYPES := c.TYPES++ds} = true := by
  apply (CandidateNestedReady.nestedTableReady_true_iff _).2
  intro p hp
  let dt := (c.TYPES++ds)[p]'hp
  have he : (c.TYPES++ds)[p]? = some dt := List.getElem?_eq_getElem hp
  have hm : dt ∈ c.TYPES := by
    have hmem := List.mem_iff_getElem?.2 ⟨p,he⟩
    rcases List.mem_append.1 hmem with h | h
    · exact h
    · exact hd dt h
  obtain ⟨k,hk⟩ := List.mem_iff_getElem?.1 hm
  obtain ⟨dt',fin,hs,st,hk',hu,hrefs⟩ :=
    (CandidateNestedReady.nestedTableReady_true_iff c).1 hn k
      (List.getElem?_eq_some_iff.1 hk).1
  have hdt : dt'=dt := Option.some.inj (hk'.symm.trans hk)
  subst dt'
  refine ⟨dt,fin,hs,st,he,hu,?_⟩
  intro ht hht
  rcases hrefs ht hht with hb | ⟨q,dq,hq,hhtq⟩
  · exact Or.inl hb
  · refine Or.inr ⟨q,dq,?_,hhtq⟩
    simpa [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hq).1] using hq

#print axioms ready_duplicates
#print axioms nested_duplicates
end properties.wasm_module_ok.ConstructiveTypeCopyReady
