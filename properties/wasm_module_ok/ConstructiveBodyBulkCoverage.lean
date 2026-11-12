import properties.wasm_module_ok.ConstructiveBodyBulkMembers
import properties.wasm_module_ok.ConstructiveBodyBulkOriginal
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyBulkCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyBulkProductions ConstructiveBodyProductionCoverage

theorem tableCopy_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«TABLE.COPY» x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«TABLE.COPY» x y) effect ∧ finish=n := by
  obtain ⟨dest,src,hx,hy,hm⟩ := ConstructiveBodyBulkOriginal.tableCopy c stack env x y effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (tableCopy c stack env dest src hm) _ effect n finish
    (ConstructiveBodyBulkMembers.tableCopy_mem c stack env dest src hm) _ h
  simpa [hx,hy] using ConstructiveBodyBulkMembers.tableCopy_produces c stack env dest src hm

theorem tableInit_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«TABLE.INIT» x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«TABLE.INIT» x y) effect ∧ finish=n := by
  obtain ⟨dest,src,hx,hy,hm⟩ := ConstructiveBodyBulkOriginal.tableInit c stack env x y effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (tableInit c stack env dest src hm) _ effect n finish
    (ConstructiveBodyBulkMembers.tableInit_mem c stack env dest src hm) _ h
  simpa [hx,hy] using ConstructiveBodyBulkMembers.tableInit_produces c stack env dest src hm

theorem memoryCopy_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«MEMORY.COPY» x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«MEMORY.COPY» x y) effect ∧ finish=n := by
  obtain ⟨dest,src,hx,hy⟩ := ConstructiveBodyBulkOriginal.memoryCopy c stack x y effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (memoryCopy c stack env dest src) _ effect n finish
    (ConstructiveBodyBulkMembers.memoryCopy_mem c stack env dest src) _ h
  simpa [hx,hy] using ConstructiveBodyBulkMembers.memoryCopy_produces c stack env dest src

theorem memoryInit_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«MEMORY.INIT» x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«MEMORY.INIT» x y) effect ∧ finish=n := by
  obtain ⟨dest,src,hx,hy⟩ := ConstructiveBodyBulkOriginal.memoryInit c stack x y effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (memoryInit c stack env dest src) _ effect n finish
    (ConstructiveBodyBulkMembers.memoryInit_mem c stack env dest src) _ h
  simpa [hx,hy] using ConstructiveBodyBulkMembers.memoryInit_produces c stack env dest src

#print axioms tableCopy_original
#print axioms memoryInit_original
end properties.wasm_module_ok.ConstructiveBodyBulkCoverage
