import properties.wasm_module_ok.ConstructiveBodyArrayProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateCatalog
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyAggregateMetadata ConstructiveBodyStorageMetadata ConstructiveBodyAggregateProductions ConstructiveConstAggregateBuilders

structure StructField (c : context) where
  owner : StructIndex c
  entry : ConstructiveBodyLookup.Entry owner.fields
  mutability : SpecTec.«mut»
  storage : storagetype
  field : entry.value=.FieldT mutability storage

structure ArrayField (c : context) where
  owner : ArrayIndex c
  mutability : SpecTec.«mut»
  storage : storagetype
  field : owner.field=.FieldT mutability storage

def structFields (c : context) : List (StructField c) :=
  (ConstructiveConstTableSeeds.structIndices c).flatMap fun owner =>
    (ConstructiveBodyLookup.entries owner.fields).map fun entry =>
      match hf : entry.value with
      | .FieldT m st => ⟨owner,entry,m,st,hf⟩

def arrayFields (c : context) : List (ArrayField c) :=
  (ConstructiveConstTableSeeds.arrayIndices c).map fun owner =>
    match hf : owner.field with
    | .FieldT m st => ⟨owner,m,st,hf⟩

theorem structFields_complete (c : context) (f : StructField c) : f∈structFields c := by
  apply List.mem_flatMap.mpr
  refine ⟨f.owner,ConstructiveConstSeedCoverage.struct_index_mem c f.owner,?_⟩
  apply List.mem_map.mpr
  refine ⟨f.entry,ConstructiveBodyLookup.complete _ f.entry,?_⟩
  split
  next m st he =>
    have hh : m=f.mutability ∧ st=f.storage := by simpa using he.symm.trans f.field
    rcases hh with ⟨rfl,rfl⟩
    rfl

theorem arrayFields_complete (c : context) (f : ArrayField c) : f∈arrayFields c := by
  apply List.mem_map.mpr
  refine ⟨f.owner,ConstructiveConstSeedCoverage.array_index_mem c f.owner,?_⟩
  split
  next m st he =>
    have hh : m=f.mutability ∧ st=f.storage := by simpa using he.symm.trans f.field
    rcases hh with ⟨rfl,rfl⟩
    rfl

def structPlans (c : context) (stack : inferresulttype) (env : Env c) (f : StructField c) : List (Production c stack) :=
  ((getOptions f.storage).attach.map fun ext =>
    structGet c stack env f.owner f.entry f.mutability f.storage f.field ext.val ((getOptions_spec _ _).1 ext.property)) ++
  (if hm : f.mutability=.Var then
    [structSet c stack env f.owner f.entry f.storage (by simpa only [hm] using f.field)] else [])

def newPlans (c : context) (stack : inferresulttype) (env : Env c) (a : ArrayIndex c) : List (Production c stack) :=
  ((ConstructiveBodyLookup.entries c.ELEMS).flatMap fun e =>
    if hm : CandidateValMatch.candidateValMatch c (.RefT e.value) (UnpackedFieldDecision.unpackedFieldResult a.field)=true then
      [ConstructiveBodyArrayProductions.newElem c stack env a e hm] else []) ++
  (if hn : ConstructiveBodyArrayProductions.numericStorage (UnpackedFieldDecision.unpackedFieldResult a.field)=true then
    (ConstructiveBodyLookup.entries c.DATAS).map fun e => ConstructiveBodyArrayProductions.newData c stack env a e hn else [])

def mutationPlans (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) (hm : f.mutability=.Var) :
    List (Production c stack) :=
  let hf : f.owner.field=.FieldT .Var f.storage := by simpa only [hm] using f.field
  [arraySet c stack env f.owner f.storage hf,arrayFill c stack env f.owner f.storage hf] ++
  ((ConstructiveBodyLookup.entries c.ELEMS).flatMap fun e =>
    if he : CandidateValMatch.candidateValMatch c (.RefT e.value) (UnpackedFieldDecision.unpackedStorageResult f.storage)=true then
      [ConstructiveBodyArrayProductions.initElem c stack env f.owner f.storage hf e he] else []) ++
  (if hn : ConstructiveBodyArrayProductions.numericStorage (UnpackedFieldDecision.unpackedStorageResult f.storage)=true then
    (ConstructiveBodyLookup.entries c.DATAS).map fun e => ConstructiveBodyArrayProductions.initData c stack env f.owner f.storage hf e hn else []) ++
  ((arrayFields c).flatMap fun g =>
    if he : storageMatch c g.storage f.storage=true then
      [ConstructiveBodyArrayProductions.copy c stack env f.owner g.owner f.storage g.storage g.mutability hf g.field he] else [])

def arrayPlans (c : context) (stack : inferresulttype) (env : Env c) (f : ArrayField c) : List (Production c stack) :=
  ((getOptions f.storage).attach.map fun ext =>
    arrayGet c stack env f.owner f.mutability f.storage f.field ext.val ((getOptions_spec _ _).1 ext.property)) ++
  (if hm : f.mutability=.Var then mutationPlans c stack env f hm else [])

def all (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  ((structFields c).flatMap fun f => structPlans c stack env f) ++
  ((ConstructiveConstTableSeeds.arrayIndices c).flatMap fun a => newPlans c stack env a) ++
  ((arrayFields c).flatMap fun f => arrayPlans c stack env f)

#print axioms all
#print axioms structFields_complete
end properties.wasm_module_ok.ConstructiveBodyAggregateCatalog
