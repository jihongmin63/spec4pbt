import properties.wasm_module_ok.ConstructiveBodyIndexedProductions
import properties.wasm_module_ok.ConstructiveBodyProductionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyIndexedMembers
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyProductionCoverage ConstructiveBodyIndexedProductions ConstructiveBodyLookup

theorem branch (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (ts : List valtype) (hx : c.LABELS[x]?=some (ts)) :
    ∃p∈labels c stack env,Produces p (.«BR» x) := by
  unfold labels
  refine ⟨?p,?mem,?prod⟩
  case mem =>
    apply List.mem_flatMap.mpr
    refine ⟨⟨x,ts,hx⟩,complete _ _,?_⟩
    exact List.mem_cons_self
  case prod => exact ⟨_,rfl,rfl⟩

theorem branchIf (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (ts : List valtype) (hx : c.LABELS[x]?=some (ts)) :
    ∃p∈labels c stack env,Produces p (.«BR_IF» x) := by
  unfold labels
  refine ⟨?p,?mem,?prod⟩
  case mem =>
    apply List.mem_flatMap.mpr
    refine ⟨⟨x,ts,hx⟩,complete _ _,?_⟩
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  case prod => exact ⟨_,rfl,rfl⟩

theorem tableGet (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype) (hx : c.TABLES[x]?=some (.TableT addr lim rt)) :
    ∃p∈tables c stack env,Produces p (.«TABLE.GET» x) := by
  unfold tables
  refine ⟨?p,?mem,?prod⟩
  case mem =>
    apply List.mem_flatMap.mpr
    refine ⟨⟨x,.TableT addr lim rt,hx⟩,complete _ _,?_⟩
    exact List.mem_cons_self
  case prod => exact ⟨_,rfl,rfl⟩

theorem tableSet (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype) (hx : c.TABLES[x]?=some (.TableT addr lim rt)) :
    ∃p∈tables c stack env,Produces p (.«TABLE.SET» x) := by
  unfold tables
  refine ⟨?p,?mem,?prod⟩
  case mem =>
    apply List.mem_flatMap.mpr
    refine ⟨⟨x,.TableT addr lim rt,hx⟩,complete _ _,?_⟩
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  case prod => exact ⟨_,rfl,rfl⟩

theorem tableSize (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype) (hx : c.TABLES[x]?=some (.TableT addr lim rt)) :
    ∃p∈tables c stack env,Produces p (.«TABLE.SIZE» x) := by
  unfold tables
  refine ⟨?p,?mem,?prod⟩
  case mem =>
    apply List.mem_flatMap.mpr
    refine ⟨⟨x,.TableT addr lim rt,hx⟩,complete _ _,?_⟩
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  case prod => exact ⟨_,rfl,rfl⟩

theorem tableGrow (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype) (hx : c.TABLES[x]?=some (.TableT addr lim rt)) :
    ∃p∈tables c stack env,Produces p (.«TABLE.GROW» x) := by
  unfold tables
  refine ⟨?p,?mem,?prod⟩
  case mem =>
    apply List.mem_flatMap.mpr
    refine ⟨⟨x,.TableT addr lim rt,hx⟩,complete _ _,?_⟩
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  case prod => exact ⟨_,rfl,rfl⟩

theorem tableFill (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (addr : addrtype) (lim : limits) (rt : reftype) (hx : c.TABLES[x]?=some (.TableT addr lim rt)) :
    ∃p∈tables c stack env,Produces p (.«TABLE.FILL» x) := by
  unfold tables
  refine ⟨?p,?mem,?prod⟩
  case mem =>
    apply List.mem_flatMap.mpr
    refine ⟨⟨x,.TableT addr lim rt,hx⟩,complete _ _,?_⟩
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  case prod => exact ⟨_,rfl,rfl⟩

theorem memorySize (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (addr : addrtype) (lim : limits) (hx : c.MEMS[x]?=some (.MemoryT addr lim)) :
    ∃p∈memories c stack env,Produces p (.«MEMORY.SIZE» x) := by
  unfold memories
  refine ⟨?p,?mem,?prod⟩
  case mem =>
    apply List.mem_flatMap.mpr
    refine ⟨⟨x,.MemoryT addr lim,hx⟩,complete _ _,?_⟩
    exact List.mem_cons_self
  case prod => exact ⟨_,rfl,rfl⟩

theorem memoryGrow (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (addr : addrtype) (lim : limits) (hx : c.MEMS[x]?=some (.MemoryT addr lim)) :
    ∃p∈memories c stack env,Produces p (.«MEMORY.GROW» x) := by
  unfold memories
  refine ⟨?p,?mem,?prod⟩
  case mem =>
    apply List.mem_flatMap.mpr
    refine ⟨⟨x,.MemoryT addr lim,hx⟩,complete _ _,?_⟩
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  case prod => exact ⟨_,rfl,rfl⟩

theorem memoryFill (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (addr : addrtype) (lim : limits) (hx : c.MEMS[x]?=some (.MemoryT addr lim)) :
    ∃p∈memories c stack env,Produces p (.«MEMORY.FILL» x) := by
  unfold memories
  refine ⟨?p,?mem,?prod⟩
  case mem =>
    apply List.mem_flatMap.mpr
    refine ⟨⟨x,.MemoryT addr lim,hx⟩,complete _ _,?_⟩
    apply List.mem_cons_of_mem
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  case prod => exact ⟨_,rfl,rfl⟩

theorem globalGet (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (mu : SpecTec.«mut») (t : valtype) (hx : c.GLOBALS[x]?=some (.GlobalT mu t)) :
    ∃p∈globals c stack env,Produces p (.«GLOBAL.GET» x) := by
  cases mu with
  | Cons =>
    unfold globals
    refine ⟨?p,?mem,?prod⟩
    case mem =>
      apply List.mem_flatMap.mpr
      refine ⟨⟨x,_,hx⟩,complete _ _,?_⟩
      exact List.mem_cons_self
    case prod => exact ⟨_,rfl,rfl⟩
  | Var =>
    unfold globals
    refine ⟨?pVar,?memVar,?prodVar⟩
    case memVar =>
      apply List.mem_flatMap.mpr
      refine ⟨⟨x,_,hx⟩,complete _ _,?_⟩
      exact List.mem_cons_self
    case prodVar => exact ⟨_,rfl,rfl⟩


theorem globalSet (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (t : valtype) (hx : c.GLOBALS[x]?=some (.GlobalT .Var t)) :
    ∃p∈globals c stack env,Produces p (.«GLOBAL.SET» x) := by
  unfold globals
  refine ⟨?p,?mem,?prod⟩
  case mem =>
    apply List.mem_flatMap.mpr
    refine ⟨⟨x,_,hx⟩,complete _ _,?_⟩
    apply List.mem_cons_of_mem
    exact List.mem_cons_self
  case prod => exact ⟨_,rfl,rfl⟩

theorem elemDrop (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (hx : x<c.ELEMS.length) :
    ∃p∈drops c stack env,Produces p (.«ELEM.DROP» x) := by
  refine ⟨_,List.mem_append_left _ (List.mem_map.mpr ⟨⟨x,hx⟩,by simp,rfl⟩),?_⟩
  exact ⟨_,rfl,rfl⟩

theorem dataDrop (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (hx : x<c.DATAS.length) :
    ∃p∈drops c stack env,Produces p (.«DATA.DROP» x) := by
  refine ⟨_,List.mem_append_right _ (List.mem_map.mpr ⟨⟨x,hx⟩,by simp,rfl⟩),?_⟩
  exact ⟨_,rfl,rfl⟩

#print axioms tableFill
#print axioms memoryFill
#print axioms globalGet
end properties.wasm_module_ok.ConstructiveBodyIndexedMembers
