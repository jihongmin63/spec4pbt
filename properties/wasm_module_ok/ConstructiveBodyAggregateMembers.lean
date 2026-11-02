import properties.wasm_module_ok.ConstructiveBodyAggregateCatalog
import properties.wasm_module_ok.ConstructiveBodyProductionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateMembers
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyAggregateCatalog ConstructiveBodyAggregateProductions ConstructiveBodyArrayProductions ConstructiveBodyStorageMetadata ConstructiveBodyProductionCoverage ConstructiveConstAggregateBuilders

theorem from_struct (c : context) (stack : inferresulttype) (env : Env c) (f : StructField c) (p : Production c stack)
    (hp : p∈structPlans c stack env f) : p∈all c stack env := by
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨f,structFields_complete c f,hp⟩

theorem from_new (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) (p : Production c stack)
    (hp : p∈newPlans c stack env a) : p∈all c stack env := by
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨a,ConstructiveConstSeedCoverage.array_index_mem c a,hp⟩

theorem from_array (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) (p : Production c stack)
    (hp : p∈arrayPlans c stack env f) : p∈all c stack env := by
  apply List.mem_append_right
  exact List.mem_flatMap.mpr ⟨f,arrayFields_complete c f,hp⟩

theorem from_mutation (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) (hm : f.mutability=.Var) (p : Production c stack)
    (hp : p∈mutationPlans c stack env f hm) : p∈all c stack env := by
  apply from_array c stack env f p
  apply List.mem_append_right
  simpa only [hm,dite_true] using hp

theorem structGet_mem (c : context) (stack : inferresulttype) (env : Env c) (f : StructField c)
    (ext : Option extension) (he : ext.isSome=packed f.storage) : structGet c stack env f.owner f.entry f.mutability f.storage f.field ext he∈all c stack env := by
  apply from_struct c stack env f
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨⟨ext,(getOptions_spec _ _).2 he⟩,by simp,rfl⟩

theorem structGet_produces (c : context) (stack : inferresulttype) (env : Env c) (f : StructField c)
    (ext : Option extension) (he : ext.isSome=packed f.storage) : Produces (structGet c stack env f.owner f.entry f.mutability f.storage f.field ext he) (.«STRUCT.GET» f.owner.index f.entry.index ext) := by
  unfold Produces structGet fixedList ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem arrayGet_mem (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c)
    (ext : Option extension) (he : ext.isSome=packed f.storage) : arrayGet c stack env f.owner f.mutability f.storage f.field ext he∈all c stack env := by
  apply from_array c stack env f
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨⟨ext,(getOptions_spec _ _).2 he⟩,by simp,rfl⟩

theorem arrayGet_produces (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c)
    (ext : Option extension) (he : ext.isSome=packed f.storage) : Produces (arrayGet c stack env f.owner f.mutability f.storage f.field ext he) (.«ARRAY.GET» f.owner.index ext) := by
  unfold Produces arrayGet fixedList ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem structSet_mem (c : context) (stack : inferresulttype) (env : Env c) (f : StructField c) (hm : f.mutability=.Var) :
    structSet c stack env f.owner f.entry f.storage (by simpa only [hm] using f.field)∈all c stack env := by
  apply from_struct c stack env f
  apply List.mem_append_right
  simp only [hm,dite_true]
  exact List.mem_singleton_self _

theorem structSet_produces (c : context) (stack : inferresulttype) (env : Env c) (f : StructField c) (hm : f.mutability=.Var) :
    Produces (structSet c stack env f.owner f.entry f.storage (by simpa only [hm] using f.field)) (.«STRUCT.SET» f.owner.index f.entry.index) := by
  unfold Produces structSet fixedList ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem arraySet_mem (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) (hm : f.mutability=.Var) :
    arraySet c stack env f.owner f.storage (by simpa only [hm] using f.field)∈all c stack env := by
  apply from_mutation c stack env f hm
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_cons_self

theorem arraySet_produces (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) (hm : f.mutability=.Var) :
    Produces (arraySet c stack env f.owner f.storage (by simpa only [hm] using f.field)) (.«ARRAY.SET» f.owner.index) := by
  unfold Produces arraySet fixedList ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem arrayFill_mem (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) (hm : f.mutability=.Var) :
    arrayFill c stack env f.owner f.storage (by simpa only [hm] using f.field)∈all c stack env := by
  apply from_mutation c stack env f hm
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_cons_of_mem _ (List.mem_singleton_self _ )

theorem arrayFill_produces (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) (hm : f.mutability=.Var) :
    Produces (arrayFill c stack env f.owner f.storage (by simpa only [hm] using f.field)) (.«ARRAY.FILL» f.owner.index) := by
  unfold Produces arrayFill fixedList ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem newElem_mem (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) (e : ConstructiveBodyLookup.Entry c.ELEMS)
    (he : CandidateValMatch.candidateValMatch c (.RefT e.value) (UnpackedFieldDecision.unpackedFieldResult a.field)=true) : newElem c stack env a e he∈all c stack env := by
  apply from_new c stack env a
  apply List.mem_append_left
  apply List.mem_flatMap.mpr
  refine ⟨e,ConstructiveBodyLookup.complete _ e,?_⟩
  simp only [he,dite_true]
  exact List.mem_singleton_self _

theorem newElem_produces (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) (e : ConstructiveBodyLookup.Entry c.ELEMS)
    (he : CandidateValMatch.candidateValMatch c (.RefT e.value) (UnpackedFieldDecision.unpackedFieldResult a.field)=true) : Produces (newElem c stack env a e he) (.«ARRAY.NEW_ELEM» a.index e.index) := by
  unfold Produces newElem fixedList ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem newData_mem (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) (e : ConstructiveBodyLookup.Entry c.DATAS)
    (he : numericStorage (UnpackedFieldDecision.unpackedFieldResult a.field)=true) : newData c stack env a e he∈all c stack env := by
  apply from_new c stack env a
  apply List.mem_append_right
  simp only [he,dite_true]
  exact List.mem_map.mpr ⟨e,ConstructiveBodyLookup.complete _ e,rfl⟩

theorem newData_produces (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) (e : ConstructiveBodyLookup.Entry c.DATAS)
    (he : numericStorage (UnpackedFieldDecision.unpackedFieldResult a.field)=true) : Produces (newData c stack env a e he) (.«ARRAY.NEW_DATA» a.index e.index) := by
  unfold Produces newData fixedList ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem initElem_mem (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) (hm : f.mutability=.Var) (e : ConstructiveBodyLookup.Entry c.ELEMS)
    (he : CandidateValMatch.candidateValMatch c (.RefT e.value) (UnpackedFieldDecision.unpackedStorageResult f.storage)=true) : initElem c stack env f.owner f.storage (by simpa only [hm] using f.field) e he∈all c stack env := by
  apply from_mutation c stack env f hm
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨e,ConstructiveBodyLookup.complete _ e,?_⟩
  simp only [he,dite_true]
  exact List.mem_singleton_self _

theorem initElem_produces (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) (hm : f.mutability=.Var) (e : ConstructiveBodyLookup.Entry c.ELEMS)
    (he : CandidateValMatch.candidateValMatch c (.RefT e.value) (UnpackedFieldDecision.unpackedStorageResult f.storage)=true) : Produces (initElem c stack env f.owner f.storage (by simpa only [hm] using f.field) e he) (.«ARRAY.INIT_ELEM» f.owner.index e.index) := by
  unfold Produces initElem fixedList ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem initData_mem (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) (hm : f.mutability=.Var) (e : ConstructiveBodyLookup.Entry c.DATAS)
    (he : numericStorage (UnpackedFieldDecision.unpackedStorageResult f.storage)=true) : initData c stack env f.owner f.storage (by simpa only [hm] using f.field) e he∈all c stack env := by
  apply from_mutation c stack env f hm
  apply List.mem_append_left
  apply List.mem_append_right
  simp only [he,dite_true]
  exact List.mem_map.mpr ⟨e,ConstructiveBodyLookup.complete _ e,rfl⟩

theorem initData_produces (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) (hm : f.mutability=.Var) (e : ConstructiveBodyLookup.Entry c.DATAS)
    (he : numericStorage (UnpackedFieldDecision.unpackedStorageResult f.storage)=true) : Produces (initData c stack env f.owner f.storage (by simpa only [hm] using f.field) e he) (.«ARRAY.INIT_DATA» f.owner.index e.index) := by
  unfold Produces initData fixedList ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem copy_mem (c : context) (stack : inferresulttype) (env : Env c) (f g : ArrayField c) (hm : f.mutability=.Var)
    (he : storageMatch c g.storage f.storage=true) :
    copy c stack env f.owner g.owner f.storage g.storage g.mutability (by simpa only [hm] using f.field) g.field he∈all c stack env := by
  apply from_mutation c stack env f hm
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨g,arrayFields_complete c g,?_⟩
  simp only [he,dite_true]
  exact List.mem_singleton_self _

theorem copy_produces (c : context) (stack : inferresulttype) (env : Env c) (f g : ArrayField c) (hm : f.mutability=.Var)
    (he : storageMatch c g.storage f.storage=true) :
    Produces (copy c stack env f.owner g.owner f.storage g.storage g.mutability (by simpa only [hm] using f.field) g.field he) (.«ARRAY.COPY» f.owner.index g.owner.index) := by
  unfold Produces copy fixedList ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

#print axioms copy_mem
end properties.wasm_module_ok.ConstructiveBodyAggregateMembers
