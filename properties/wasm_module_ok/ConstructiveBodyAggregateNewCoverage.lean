import properties.wasm_module_ok.ConstructiveBodyAggregateNewMembers
import properties.wasm_module_ok.ConstructiveBodyAggregateNewOriginal
import properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateNewCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyAggregateNewMembers ConstructiveBodyProductionCoverage

theorem structExplicit (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish bound : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«STRUCT.NEW» x .Explicit)⟩)
      n (.success (.of effect)) finish) :
    Covers (ConstructiveBodyAggregateNew.all c stack env bound) (.«STRUCT.NEW» x .Explicit) effect ∧ finish=n := by
  obtain ⟨index,hx⟩ := ConstructiveBodyAggregateNewOriginal.structExplicit c stack x effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (ConstructiveBodyAggregateNew.all c stack env bound)
    (ConstructiveBodyAggregateNew.structExplicit c stack env index) _ effect n finish
    (structExplicit_mem c stack env index bound) _ h
  simpa only [hx] using structExplicit_produces c stack env index

theorem structImplicit (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish bound : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«STRUCT.NEW» x .Implicit)⟩)
      n (.success (.of effect)) finish) :
    Covers (ConstructiveBodyAggregateNew.all c stack env bound) (.«STRUCT.NEW» x .Implicit) effect ∧ finish=n := by
  obtain ⟨index,hx,hd⟩ := ConstructiveBodyAggregateNewOriginal.structImplicit c stack x effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (ConstructiveBodyAggregateNew.all c stack env bound)
    (ConstructiveBodyAggregateNew.structImplicit c stack env index hd) _ effect n finish
    (structImplicit_mem c stack env index hd bound) _ h
  simpa only [hx] using structImplicit_produces c stack env index hd

theorem arrayExplicit (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish bound : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«ARRAY.NEW» x .Explicit)⟩)
      n (.success (.of effect)) finish) :
    Covers (ConstructiveBodyAggregateNew.all c stack env bound) (.«ARRAY.NEW» x .Explicit) effect ∧ finish=n := by
  obtain ⟨index,hx⟩ := ConstructiveBodyAggregateNewOriginal.arrayExplicit c stack x effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (ConstructiveBodyAggregateNew.all c stack env bound)
    (ConstructiveBodyAggregateNew.arrayExplicit c stack env index) _ effect n finish
    (arrayExplicit_mem c stack env index bound) _ h
  simpa only [hx] using arrayExplicit_produces c stack env index

theorem arrayImplicit (c : context) (stack : inferresulttype) (env : Env c) (x : Nat)
    (effect : inferinstrtype) (n finish bound : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«ARRAY.NEW» x .Implicit)⟩)
      n (.success (.of effect)) finish) :
    Covers (ConstructiveBodyAggregateNew.all c stack env bound) (.«ARRAY.NEW» x .Implicit) effect ∧ finish=n := by
  obtain ⟨index,hx,hd⟩ := ConstructiveBodyAggregateNewOriginal.arrayImplicit c stack x effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (ConstructiveBodyAggregateNew.all c stack env bound)
    (ConstructiveBodyAggregateNew.arrayImplicit c stack env index hd) _ effect n finish
    (arrayImplicit_mem c stack env index hd bound) _ h
  simpa only [hx] using arrayImplicit_produces c stack env index hd

theorem arrayFixed (c : context) (stack : inferresulttype) (env : Env c) (x : Nat) (count : Nat)
    (effect : inferinstrtype) (n finish bound : Nat) (hc : count≤bound)
    (h : SpecTecExecution.Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«ARRAY.NEW_FIXED» x count)⟩)
      n (.success (.of effect)) finish) :
    Covers (ConstructiveBodyAggregateNew.all c stack env bound) (.«ARRAY.NEW_FIXED» x count) effect ∧ finish=n := by
  obtain ⟨index,hx⟩ := ConstructiveBodyAggregateNewOriginal.arrayFixed c stack x count effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (ConstructiveBodyAggregateNew.all c stack env bound)
    (ConstructiveBodyAggregateNew.arrayFixed c stack env index count) _ effect n finish
    (arrayFixed_mem c stack env index count bound hc) _ h
  simpa only [hx] using arrayFixed_produces c stack env index count

#print axioms arrayFixed
end properties.wasm_module_ok.ConstructiveBodyAggregateNewCoverage
