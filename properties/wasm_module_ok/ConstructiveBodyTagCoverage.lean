import properties.wasm_module_ok.ConstructiveBodyTagMetadata
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyTagCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyTagMetadata

theorem tags_complete (c : context) (tag : Tag c) : tag∈tags c := by
  have hx := (List.getElem?_eq_some_iff.mp tag.lookup).1
  have hget : c.TAGS[tag.index]=.TagT tag.definition := (List.getElem?_eq_some_iff.mp tag.lookup).2
  apply List.mem_flatMap.mpr
  refine ⟨⟨tag.index,hx⟩,by simp,?_⟩
  split
  next dt ht =>
    have hdt : dt=tag.definition := by rw [ht] at hget; exact tagtype.TagT.inj hget
    subst dt
    split
    next ins outs he =>
      have hh : ins=tag.inputs ∧ outs=tag.outputs := by
        have hp := tag.expanded
        rw [he] at hp
        simpa using hp
      rcases hh with ⟨rfl,rfl⟩
      exact List.mem_singleton_self _
    next he =>
      have hp := tag.expanded
      exact (he tag.inputs tag.outputs hp).elim

#print axioms tags_complete
end properties.wasm_module_ok.ConstructiveBodyTagCoverage
