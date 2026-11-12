import properties.wasm_module_ok.ConstructiveBodyLookup
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyIndexedTypes
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment

structure Table (c : context) where
  index : Nat
  addr : addrtype
  lim : limits
  rt : reftype
  lookup : c.TABLES[index]?=some (.TableT addr lim rt)

structure Memory (c : context) where
  index : Nat
  addr : addrtype
  lim : limits
  lookup : c.MEMS[index]?=some (.MemoryT addr lim)

def tables (c : context) : List (Table c) :=
  (ConstructiveBodyLookup.entries c.TABLES).map fun e =>
    match he : e.value with
    | .TableT addr lim rt => ⟨e.index,addr,lim,rt,by simpa [he] using e.lookup⟩

def memories (c : context) : List (Memory c) :=
  (ConstructiveBodyLookup.entries c.MEMS).map fun e =>
    match he : e.value with
    | .MemoryT addr lim => ⟨e.index,addr,lim,by simpa [he] using e.lookup⟩

theorem tables_complete (c : context) (tab : Table c) : tab∈tables c := by
  apply List.mem_map.mpr
  let e : ConstructiveBodyLookup.Entry c.TABLES := ⟨tab.index,.TableT tab.addr tab.lim tab.rt,tab.lookup⟩
  exact ⟨e,ConstructiveBodyLookup.complete _ e,rfl⟩

theorem memories_complete (c : context) (mem : Memory c) : mem∈memories c := by
  apply List.mem_map.mpr
  let e : ConstructiveBodyLookup.Entry c.MEMS := ⟨mem.index,.MemoryT mem.addr mem.lim,mem.lookup⟩
  exact ⟨e,ConstructiveBodyLookup.complete _ e,rfl⟩

theorem Table.backed {c : context} (tab : Table c) (env : Env c) :
    CandidateValMatch.InTableVal c (.RefT tab.rt) :=
  env.tables tab.addr tab.lim tab.rt (List.mem_iff_getElem?.mpr ⟨tab.index,tab.lookup⟩)

#print axioms tables_complete
#print axioms memories_complete
end properties.wasm_module_ok.ConstructiveBodyIndexedTypes
