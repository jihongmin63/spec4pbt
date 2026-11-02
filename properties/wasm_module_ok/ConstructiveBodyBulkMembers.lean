import properties.wasm_module_ok.ConstructiveBodyBulkProductions
import properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyBulkMembers
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyIndexedTypes ConstructiveBodyBulkProductions ConstructiveBodyProductionCoverage

theorem tableCopy_mem (c : context) (stack : inferresulttype) (env : Env c) (dest : Table c) (src : Table c)
    (hm : ConstructiveBodyReferenceMatcher.refMatch c src.rt dest.rt=true) :
    tableCopy c stack env dest src hm∈all c stack env := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨dest,ConstructiveBodyIndexedTypes.tables_complete c dest,?_⟩
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨src,ConstructiveBodyIndexedTypes.tables_complete c src,?_⟩
  simp only [hm,dite_true]
  exact List.mem_singleton_self _

theorem tableCopy_produces (c : context) (stack : inferresulttype) (env : Env c) (dest : Table c) (src : Table c)
    (hm : ConstructiveBodyReferenceMatcher.refMatch c src.rt dest.rt=true) :
    Produces (tableCopy c stack env dest src hm) (.«TABLE.COPY» dest.index src.index) := by
  unfold Produces tableCopy ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem tableInit_mem (c : context) (stack : inferresulttype) (env : Env c) (dest : Table c) (src : ConstructiveBodyLookup.Entry c.ELEMS)
    (hm : ConstructiveBodyReferenceMatcher.refMatch c src.value dest.rt=true) :
    tableInit c stack env dest src hm∈all c stack env := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨dest,ConstructiveBodyIndexedTypes.tables_complete c dest,?_⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨src,ConstructiveBodyLookup.complete _ src,?_⟩
  simp only [hm,dite_true]
  exact List.mem_singleton_self _

theorem tableInit_produces (c : context) (stack : inferresulttype) (env : Env c) (dest : Table c) (src : ConstructiveBodyLookup.Entry c.ELEMS)
    (hm : ConstructiveBodyReferenceMatcher.refMatch c src.value dest.rt=true) :
    Produces (tableInit c stack env dest src hm) (.«TABLE.INIT» dest.index src.index) := by
  unfold Produces tableInit ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem memoryCopy_mem (c : context) (stack : inferresulttype) (env : Env c) (dest : Memory c) (src : Memory c) :
    memoryCopy c stack env dest src∈all c stack env := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨dest,ConstructiveBodyIndexedTypes.memories_complete c dest,?_⟩
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨src,ConstructiveBodyIndexedTypes.memories_complete c src,rfl⟩

theorem memoryCopy_produces (c : context) (stack : inferresulttype) (env : Env c) (dest : Memory c) (src : Memory c) :
    Produces (memoryCopy c stack env dest src) (.«MEMORY.COPY» dest.index src.index) := by
  unfold Produces memoryCopy ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem memoryInit_mem (c : context) (stack : inferresulttype) (env : Env c) (dest : Memory c) (src : Fin c.DATAS.length) :
    memoryInit c stack env dest src∈all c stack env := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨dest,ConstructiveBodyIndexedTypes.memories_complete c dest,?_⟩
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨src,by simp,rfl⟩

theorem memoryInit_produces (c : context) (stack : inferresulttype) (env : Env c) (dest : Memory c) (src : Fin c.DATAS.length) :
    Produces (memoryInit c stack env dest src) (.«MEMORY.INIT» dest.index src.val) := by
  unfold Produces memoryInit ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

#print axioms tableCopy_mem
end properties.wasm_module_ok.ConstructiveBodyBulkMembers
