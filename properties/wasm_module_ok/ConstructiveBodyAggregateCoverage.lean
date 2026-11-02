import properties.wasm_module_ok.ConstructiveBodyAggregateMembers
import properties.wasm_module_ok.ConstructiveBodyAggregateAccessOriginal
import properties.wasm_module_ok.ConstructiveBodyArrayBulkOriginal
import properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductionCoverage ConstructiveBodyAggregateCatalog ConstructiveBodyAggregateProductions ConstructiveBodyArrayProductions

theorem structGetSome_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat) (ext : extension)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«STRUCT.GET» x y (some ext))⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«STRUCT.GET» x y (some ext)) effect ∧ finish=n := by
  obtain ⟨f,hx,hy,hp⟩ := ConstructiveBodyAggregateAccessOriginal.structGetSome c stack x y ext effect n finish h
  have he : ((some ext) : Option extension).isSome=ConstructiveBodyStorageMetadata.packed f.storage := hp.symm
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (structGet c stack env f.owner f.entry f.mutability f.storage f.field (some ext) he) _ effect n finish
    (ConstructiveBodyAggregateMembers.structGet_mem c stack env f (some ext) he) _ h
  simpa only [hx,hy] using ConstructiveBodyAggregateMembers.structGet_produces c stack env f (some ext) he

theorem structGetNone_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«STRUCT.GET» x y none)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«STRUCT.GET» x y none) effect ∧ finish=n := by
  obtain ⟨f,hx,hy,hp⟩ := ConstructiveBodyAggregateAccessOriginal.structGetNone c stack x y effect n finish h
  have he : (none : Option extension).isSome=ConstructiveBodyStorageMetadata.packed f.storage := by simpa only [Option.isSome_none] using (Bool.eq_false_iff.mpr hp).symm
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (structGet c stack env f.owner f.entry f.mutability f.storage f.field none he) _ effect n finish
    (ConstructiveBodyAggregateMembers.structGet_mem c stack env f none he) _ h
  simpa only [hx,hy] using ConstructiveBodyAggregateMembers.structGet_produces c stack env f none he

theorem structSet_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«STRUCT.SET» x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«STRUCT.SET» x y) effect ∧ finish=n := by
  obtain ⟨f,hx,hy,hm⟩ := ConstructiveBodyAggregateAccessOriginal.structSet c stack x y effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (structSet c stack env f.owner f.entry f.storage (by simpa only [hm] using f.field)) _ effect n finish
    (ConstructiveBodyAggregateMembers.structSet_mem c stack env f hm) _ h
  simpa only [hx,hy] using ConstructiveBodyAggregateMembers.structSet_produces c stack env f hm

theorem arrayGetSome_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (ext : extension)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.GET» x (some ext))⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«ARRAY.GET» x (some ext)) effect ∧ finish=n := by
  obtain ⟨f,hx,hp⟩ := ConstructiveBodyAggregateAccessOriginal.arrayGetSome c stack x ext effect n finish h
  have he : ((some ext) : Option extension).isSome=ConstructiveBodyStorageMetadata.packed f.storage := hp.symm
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (arrayGet c stack env f.owner f.mutability f.storage f.field (some ext) he) _ effect n finish
    (ConstructiveBodyAggregateMembers.arrayGet_mem c stack env f (some ext) he) _ h
  simpa only [hx] using ConstructiveBodyAggregateMembers.arrayGet_produces c stack env f (some ext) he

theorem arrayGetNone_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.GET» x none)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«ARRAY.GET» x none) effect ∧ finish=n := by
  obtain ⟨f,hx,hp⟩ := ConstructiveBodyAggregateAccessOriginal.arrayGetNone c stack x effect n finish h
  have he : (none : Option extension).isSome=ConstructiveBodyStorageMetadata.packed f.storage := by simpa only [Option.isSome_none] using (Bool.eq_false_iff.mpr hp).symm
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (arrayGet c stack env f.owner f.mutability f.storage f.field none he) _ effect n finish
    (ConstructiveBodyAggregateMembers.arrayGet_mem c stack env f none he) _ h
  simpa only [hx] using ConstructiveBodyAggregateMembers.arrayGet_produces c stack env f none he

theorem arraySet_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.SET» x)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«ARRAY.SET» x) effect ∧ finish=n := by
  obtain ⟨f,hx,hm⟩ := ConstructiveBodyAggregateAccessOriginal.arraySet c stack x effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (arraySet c stack env f.owner f.storage (by simpa only [hm] using f.field)) _ effect n finish
    (ConstructiveBodyAggregateMembers.arraySet_mem c stack env f hm) _ h
  simpa only [hx] using ConstructiveBodyAggregateMembers.arraySet_produces c stack env f hm

theorem arrayFill_original (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.FILL» x)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«ARRAY.FILL» x) effect ∧ finish=n := by
  obtain ⟨f,hx,hm⟩ := ConstructiveBodyAggregateAccessOriginal.arrayFill c stack x effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (arrayFill c stack env f.owner f.storage (by simpa only [hm] using f.field)) _ effect n finish
    (ConstructiveBodyAggregateMembers.arrayFill_mem c stack env f hm) _ h
  simpa only [hx] using ConstructiveBodyAggregateMembers.arrayFill_produces c stack env f hm

theorem newElem_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.NEW_ELEM» x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«ARRAY.NEW_ELEM» x y) effect ∧ finish=n := by
  obtain ⟨a,e,hx,hy,he⟩ := ConstructiveBodyArrayBulkOriginal.newElem c stack env x y effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (newElem c stack env a e he) _ effect n finish
    (ConstructiveBodyAggregateMembers.newElem_mem c stack env a e he) _ h
  simpa only [hx,hy] using ConstructiveBodyAggregateMembers.newElem_produces c stack env a e he

theorem newData_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.NEW_DATA» x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«ARRAY.NEW_DATA» x y) effect ∧ finish=n := by
  obtain ⟨a,e,hx,hy,he⟩ := ConstructiveBodyArrayBulkOriginal.newData c stack env x y effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (newData c stack env a e he) _ effect n finish
    (ConstructiveBodyAggregateMembers.newData_mem c stack env a e he) _ h
  simpa only [hx,hy] using ConstructiveBodyAggregateMembers.newData_produces c stack env a e he

theorem initElem_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.INIT_ELEM» x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«ARRAY.INIT_ELEM» x y) effect ∧ finish=n := by
  obtain ⟨f,e,hx,hy,hm,he⟩ := ConstructiveBodyArrayBulkOriginal.initElem c stack env x y effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (initElem c stack env f.owner f.storage (by simpa only [hm] using f.field) e he) _ effect n finish
    (ConstructiveBodyAggregateMembers.initElem_mem c stack env f hm e he) _ h
  simpa only [hx,hy] using ConstructiveBodyAggregateMembers.initElem_produces c stack env f hm e he

theorem initData_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.INIT_DATA» x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«ARRAY.INIT_DATA» x y) effect ∧ finish=n := by
  obtain ⟨f,e,hx,hy,hm,he⟩ := ConstructiveBodyArrayBulkOriginal.initData c stack env x y effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (initData c stack env f.owner f.storage (by simpa only [hm] using f.field) e he) _ effect n finish
    (ConstructiveBodyAggregateMembers.initData_mem c stack env f hm e he) _ h
  simpa only [hx,hy] using ConstructiveBodyAggregateMembers.initData_produces c stack env f hm e he

theorem copy_original (c : context) (stack : inferresulttype) (env : Env c) (x y : Nat)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ARRAY.COPY» x y)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env) (.«ARRAY.COPY» x y) effect ∧ finish=n := by
  obtain ⟨f,g,hx,hy,hm,he⟩ := ConstructiveBodyArrayBulkOriginal.copy c stack env x y effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) (copy c stack env f.owner g.owner f.storage g.storage g.mutability (by simpa only [hm] using f.field) g.field he) _ effect n finish
    (ConstructiveBodyAggregateMembers.copy_mem c stack env f g hm he) _ h
  simpa only [hx,hy] using ConstructiveBodyAggregateMembers.copy_produces c stack env f g hm he

#print axioms structGetSome_original
#print axioms copy_original
end properties.wasm_module_ok.ConstructiveBodyAggregateCoverage
