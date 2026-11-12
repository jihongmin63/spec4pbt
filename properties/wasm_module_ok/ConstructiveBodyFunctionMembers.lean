import properties.wasm_module_ok.ConstructiveBodyFunctionProductions
import properties.wasm_module_ok.ConstructiveBodyProductionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyFunctionMembers
open SpecTec properties.wasm_module_ok ConstructiveBodyFunctionMetadata ConstructiveBodyEnvironment ConstructiveBodyFunctionProductions ConstructiveBodyProductionCoverage

theorem tables_complete (c : context) (tab : FunctionTable c) : tab∈functionTables c := by
  apply List.mem_flatMap.mpr
  let e : ConstructiveBodyLookup.Entry c.TABLES := ⟨tab.index,.TableT tab.addr tab.lim tab.rt,tab.lookup⟩
  refine ⟨e,ConstructiveBodyLookup.complete _ e,?_⟩
  simp only [e,tab.matched,dite_true]
  exact List.mem_singleton_self _

theorem direct_mem (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.FUNCS) :
    direct c stack env sig∈all c stack env := by
  simp only [all,List.mem_append]
  left; left
  apply List.mem_flatMap.mpr
  exact ⟨sig,complete _ sig,List.mem_append_left _ (List.mem_singleton_self _)⟩

theorem returnDirect_mem (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.FUNCS)
    (hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true) :
    returnDirect c stack env sig hm∈all c stack env := by
  simp only [all,List.mem_append]
  left; left
  apply List.mem_flatMap.mpr
  refine ⟨sig,complete _ sig,?_⟩
  apply List.mem_append_right
  simp only [hm,dite_true]
  exact List.mem_singleton_self _

theorem reference_mem (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.TYPES) :
    reference c stack env sig∈all c stack env := by
  simp only [all,List.mem_append]
  left; right
  apply List.mem_flatMap.mpr
  refine ⟨sig,complete _ sig,?_⟩
  apply List.mem_append_left
  exact List.mem_append_left _ (List.mem_singleton_self _)

theorem returnReference_mem (c : context) (stack : inferresulttype) (env : Env c) (sig : Signature c.TYPES)
    (hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true) :
    returnReference c stack env sig hm∈all c stack env := by
  simp only [all,List.mem_append]
  left; right
  apply List.mem_flatMap.mpr
  refine ⟨sig,complete _ sig,?_⟩
  apply List.mem_append_left
  apply List.mem_append_right
  simp only [hm,dite_true]
  exact List.mem_singleton_self _

theorem indirect_mem (c : context) (stack : inferresulttype) (env : Env c)
    (tab : FunctionTable c) (sig : Signature c.TYPES) :
    indirect c stack env tab sig∈all c stack env := by
  simp only [all,List.mem_append]
  left; right
  apply List.mem_flatMap.mpr
  refine ⟨sig,complete _ sig,?_⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨tab,tables_complete c tab,?_⟩
  exact List.mem_append_left _ (List.mem_singleton_self _)

theorem returnIndirect_mem (c : context) (stack : inferresulttype) (env : Env c)
    (tab : FunctionTable c) (sig : Signature c.TYPES)
    (hm : MatchResulttypeDecision.matchPairs c sig.outputs c.RESULTS=true) :
    returnIndirect c stack env tab sig hm∈all c stack env := by
  simp only [all,List.mem_append]
  left; right
  apply List.mem_flatMap.mpr
  refine ⟨sig,complete _ sig,?_⟩
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨tab,tables_complete c tab,?_⟩
  apply List.mem_append_right
  simp only [hm,dite_true]
  exact List.mem_singleton_self _

theorem throwTag_mem (c : context) (stack : inferresulttype) (env : Env c) (tag : ConstructiveBodyTagMetadata.Tag c) :
    throwTag c stack env tag∈all c stack env := by
  simp only [all,List.mem_append]
  right
  exact List.mem_map.mpr ⟨tag,ConstructiveBodyTagCoverage.tags_complete c tag,rfl⟩

#print axioms returnIndirect_mem
end properties.wasm_module_ok.ConstructiveBodyFunctionMembers
