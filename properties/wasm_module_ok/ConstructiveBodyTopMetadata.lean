import properties.wasm_module_ok.ConstructiveBodyTopHeap
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyTopMetadata
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyTopHeap

structure Shape (c : context) where
  entry : ConstructiveBodyLookup.Entry c.TYPES
  shape : strtype
  expanded : UnrollInterface.expandResult entry.value=some shape

def shapes (c : context) : List (Shape c) :=
  (ConstructiveBodyLookup.entries c.TYPES).flatMap fun e =>
    match he : UnrollInterface.expandResult e.value with
    | some st => [⟨e,st,he⟩]
    | none => []

theorem shapes_complete (c : context) (s : Shape c) : s∈shapes c := by
  apply List.mem_flatMap.mpr
  refine ⟨s.entry,ConstructiveBodyLookup.complete _ s.entry,?_⟩
  split
  next st he =>
    have hh : st=s.shape := Option.some.inj (he.symm.trans s.expanded)
    subst st
    exact List.mem_singleton_self _
  next he => rw [s.expanded] at he; cases he

theorem shape_exists (c : context) (hr : CandidateTypeReady.Ready c) (e : ConstructiveBodyLookup.Entry c.TYPES) :
    ∃s : Shape c,s.entry=e := by
  obtain ⟨dt,fin,parents,st,hx,hu,_⟩ := hr.unrolledPredecessors e.index (List.getElem?_eq_some_iff.mp e.lookup).1
  have hd : dt=e.value := Option.some.inj (hx.symm.trans e.lookup)
  subst dt
  exact ⟨⟨e,st,by simp [UnrollInterface.expandResult,hu]⟩,rfl⟩

structure Top (c : context) where
  heap : heaptype
  top : heaptype
  valid : HeaptypeValidation.heaptypeValid c heap=true
  baseTop : top∈HeaptypeValidation.baseHeaptypes
  call : ∀n,SpecTecExecution.Eval SpecTec.specTecProgram
    (.call ⟨heaptype,SpecTecCall.«$top_of_heap_type» c.TYPES heap⟩) n (.success (.of top)) n

def base (c : context) (pair : heaptype × heaptype) (hp : pair∈basePairs) : Top c :=
  ⟨pair.1,pair.2,by
    rcases pair with ⟨heap,top⟩
    simp only [basePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp <;> cases hp <;> rfl,
   by
    rcases pair with ⟨heap,top⟩
    simp only [basePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp <;> cases hp <;> simp [HeaptypeValidation.baseHeaptypes],
   fun n => base_call c pair.1 pair.2 n hp⟩

def indexed (c : context) (s : Shape c) : Top c :=
  ⟨.VarHT (.StatX s.entry.index),structuralTop s.shape,
   (HeaptypeValidation.heaptype_valid_iff c _).2 (Or.inr ⟨s.entry.index,rfl,(List.getElem?_eq_some_iff.mp s.entry.lookup).1⟩),
   by cases s.shape <;> simp [structuralTop,HeaptypeValidation.baseHeaptypes],
   fun n => static_call c s.entry.index s.entry.value s.shape n s.entry.lookup s.expanded⟩

def all (c : context) : List (Top c) :=
  basePairs.attach.map (fun p => base c p.val p.property) ++
  (shapes c).map (indexed c)

theorem base_mem (c : context) (p : heaptype × heaptype) (hp : p∈basePairs) : base c p hp∈all c :=
  List.mem_append_left _ (List.mem_map.mpr ⟨⟨p,hp⟩,by simp,rfl⟩)
theorem indexed_mem (c : context) (s : Shape c) : indexed c s∈all c :=
  List.mem_append_right _ (List.mem_map.mpr ⟨s,shapes_complete c s,rfl⟩)

#print axioms shape_exists
#print axioms all
end properties.wasm_module_ok.ConstructiveBodyTopMetadata
