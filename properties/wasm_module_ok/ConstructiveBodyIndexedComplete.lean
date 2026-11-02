import properties.wasm_module_ok.ConstructiveBodyIndexedMembers
import properties.wasm_module_ok.ConstructiveBodyIndexedCoverage
import properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyIndexedComplete
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyProductionCoverage ConstructiveBodyIndexedProductions

theorem branch (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«BR» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«BR» x) effect ∧ finish=n := by
  obtain ⟨ts,hx,_⟩ := ConstructiveBodyIndexedCoverage.branch_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.branch c stack env x ts hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem branchIf (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«BR_IF» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«BR_IF» x) effect ∧ finish=n := by
  obtain ⟨ts,hx,_⟩ := ConstructiveBodyIndexedCoverage.branchIf_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.branchIf c stack env x ts hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem globalGet (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«GLOBAL.GET» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«GLOBAL.GET» x) effect ∧ finish=n := by
  obtain ⟨mu,t,hx,_⟩ := ConstructiveBodyIndexedCoverage.globalGet_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.globalGet c stack env x mu t hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem globalSet (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«GLOBAL.SET» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«GLOBAL.SET» x) effect ∧ finish=n := by
  obtain ⟨t,hx,_⟩ := ConstructiveBodyIndexedCoverage.globalSet_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.globalSet c stack env x t hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem tableGet (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.GET» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«TABLE.GET» x) effect ∧ finish=n := by
  obtain ⟨addr,lim,rt,hx,_⟩ := ConstructiveBodyIndexedCoverage.tableGet_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.tableGet c stack env x addr lim rt hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem tableSet (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.SET» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«TABLE.SET» x) effect ∧ finish=n := by
  obtain ⟨addr,lim,rt,hx,_⟩ := ConstructiveBodyIndexedCoverage.tableSet_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.tableSet c stack env x addr lim rt hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem tableSize (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.SIZE» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«TABLE.SIZE» x) effect ∧ finish=n := by
  obtain ⟨addr,lim,rt,hx,_⟩ := ConstructiveBodyIndexedCoverage.tableSize_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.tableSize c stack env x addr lim rt hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem tableGrow (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.GROW» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«TABLE.GROW» x) effect ∧ finish=n := by
  obtain ⟨addr,lim,rt,hx,_⟩ := ConstructiveBodyIndexedCoverage.tableGrow_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.tableGrow c stack env x addr lim rt hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem tableFill (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«TABLE.FILL» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«TABLE.FILL» x) effect ∧ finish=n := by
  obtain ⟨addr,lim,rt,hx,_⟩ := ConstructiveBodyIndexedCoverage.tableFill_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.tableFill c stack env x addr lim rt hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem memorySize (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.SIZE» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«MEMORY.SIZE» x) effect ∧ finish=n := by
  obtain ⟨addr,lim,hx,_⟩ := ConstructiveBodyIndexedCoverage.memorySize_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.memorySize c stack env x addr lim hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem memoryGrow (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.GROW» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«MEMORY.GROW» x) effect ∧ finish=n := by
  obtain ⟨addr,lim,hx,_⟩ := ConstructiveBodyIndexedCoverage.memoryGrow_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.memoryGrow c stack env x addr lim hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem memoryFill (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«MEMORY.FILL» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«MEMORY.FILL» x) effect ∧ finish=n := by
  obtain ⟨addr,lim,hx,_⟩ := ConstructiveBodyIndexedCoverage.memoryFill_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.memoryFill c stack env x addr lim hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem elemDrop (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«ELEM.DROP» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«ELEM.DROP» x) effect ∧ finish=n := by
  obtain ⟨hx,_⟩ := ConstructiveBodyIndexedCoverage.elemDrop_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.elemDrop c stack env x hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

theorem dataDrop (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«DATA.DROP» x)⟩)
      n (.success (.of effect)) finish) : Covers (all c stack env) (.«DATA.DROP» x) effect ∧ finish=n := by
  obtain ⟨hx,_⟩ := ConstructiveBodyIndexedCoverage.dataDrop_original c stack x effect n finish h
  obtain ⟨p,hp,hi⟩ := ConstructiveBodyIndexedMembers.dataDrop c stack env x hx
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env) p _ effect n finish _ hi h
  simp only [all,List.mem_append]
  tauto

#print axioms branch
#print axioms globalSet
#print axioms tableFill
#print axioms memoryFill
end properties.wasm_module_ok.ConstructiveBodyIndexedComplete
