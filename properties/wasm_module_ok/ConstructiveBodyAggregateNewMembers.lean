import properties.wasm_module_ok.ConstructiveBodyAggregateNew
import properties.wasm_module_ok.ConstructiveBodyProductionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateNewMembers
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyAggregateMetadata ConstructiveBodyAggregateNew ConstructiveBodyProductionCoverage
open _root_.properties.wasm_module_ok.ConstructiveConstAggregateBuilders hiding structExplicit structImplicit arrayExplicit arrayImplicit arrayFixed

theorem structExplicit_mem (c : context) (stack : inferresulttype) (env : Env c) (s : StructIndex c)
    (bound : Nat) : structExplicit c stack env s∈all c stack env bound := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨s,ConstructiveConstSeedCoverage.struct_index_mem c s,?_⟩
  apply List.mem_append_left
  exact List.mem_singleton_self _

theorem structExplicit_produces (c : context) (stack : inferresulttype) (env : Env c) (s : StructIndex c) :
    Produces (structExplicit c stack env s) (.«STRUCT.NEW» s.index .Explicit) := by
  unfold Produces structExplicit ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem structImplicit_mem (c : context) (stack : inferresulttype) (env : Env c) (s : StructIndex c) (hd : StructImplicitFieldsDecision.structFieldsDefaultable s.fields=true)
    (bound : Nat) : structImplicit c stack env s hd∈all c stack env bound := by
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨s,ConstructiveConstSeedCoverage.struct_index_mem c s,?_⟩
  apply List.mem_append_right
  simp only [hd,dite_true]
  exact List.mem_singleton_self _

theorem structImplicit_produces (c : context) (stack : inferresulttype) (env : Env c) (s : StructIndex c) (hd : StructImplicitFieldsDecision.structFieldsDefaultable s.fields=true) :
    Produces (structImplicit c stack env s hd) (.«STRUCT.NEW» s.index .Implicit) := by
  unfold Produces structImplicit ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem arrayExplicit_mem (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c)
    (bound : Nat) : arrayExplicit c stack env a∈all c stack env bound := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨a,ConstructiveConstSeedCoverage.array_index_mem c a,?_⟩
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_singleton_self _

theorem arrayExplicit_produces (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) :
    Produces (arrayExplicit c stack env a) (.«ARRAY.NEW» a.index .Explicit) := by
  unfold Produces arrayExplicit ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem arrayImplicit_mem (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) (hd : DefaultableValidation.defaultable (UnpackedFieldDecision.unpackedFieldResult a.field)=true)
    (bound : Nat) : arrayImplicit c stack env a hd∈all c stack env bound := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨a,ConstructiveConstSeedCoverage.array_index_mem c a,?_⟩
  apply List.mem_append_left
  apply List.mem_append_right
  simp only [hd,dite_true]
  exact List.mem_singleton_self _

theorem arrayImplicit_produces (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) (hd : DefaultableValidation.defaultable (UnpackedFieldDecision.unpackedFieldResult a.field)=true) :
    Produces (arrayImplicit c stack env a hd) (.«ARRAY.NEW» a.index .Implicit) := by
  unfold Produces arrayImplicit ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem arrayFixed_mem (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) (count : Nat)
    (bound : Nat) (hc : count≤bound) : arrayFixed c stack env a count∈all c stack env bound := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨a,ConstructiveConstSeedCoverage.array_index_mem c a,?_⟩
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨count,List.mem_range.mpr (by omega),rfl⟩

theorem arrayFixed_produces (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) (count : Nat) :
    Produces (arrayFixed c stack env a count) (.«ARRAY.NEW_FIXED» a.index count) := by
  unfold Produces arrayFixed ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

#print axioms arrayFixed_mem
end properties.wasm_module_ok.ConstructiveBodyAggregateNewMembers
