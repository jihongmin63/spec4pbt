import properties.wasm_module_ok.ConstructiveBodyPayloadCoverage
import properties.wasm_module_ok.ConstructiveBodyUnaryGeneration
import properties.wasm_module_ok.ConstructiveBodyConversionGeneration
import properties.wasm_module_ok.ConstructiveBodyVectorBinaryGeneration
import properties.wasm_module_ok.ConstructiveBodyVectorLaneGeneration
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyRestrictedCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyProductionCoverage

theorem unary (c : context) (stack : inferresulttype) (env : Env c) (op : unop_) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.UNARY op)⟩) n (.success (.of effect)) finish) :
    Covers (ConstructiveBodyUnaryGeneration.all c stack env) (.UNARY op) effect ∧ finish=n := by
  obtain ⟨hl,_⟩ := ConstructiveBodyUnaryGeneration.original c stack op effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (ConstructiveBodyUnaryGeneration.all c stack env)
    (ConstructiveBodyUnaryGeneration.production c stack env (ConstructiveBodyOperatorTypes.numericType op)) _ effect n finish _ _ h
  · exact List.mem_map.mpr ⟨_,by cases ConstructiveBodyOperatorTypes.numericType op <;> simp,rfl⟩
  · unfold ConstructiveBodyUnaryGeneration.production
    apply ConstructiveBodyPayloadCoverage.mapped (a:=(⟨op,rfl,hl⟩ : {v : unop_ // ConstructiveBodyOperatorTypes.numericType v=ConstructiveBodyOperatorTypes.numericType op ∧ ConstructiveBodyUnary.legal v=true}))
    exact ConstructiveBodyUnaryGeneration.payloads_complete op hl

theorem conversion (c : context) (stack : inferresulttype) (env : Env c) (op : cvtop_) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.CONVERT op)⟩) n (.success (.of effect)) finish) :
    Covers (ConstructiveBodyConversionGeneration.all c stack env) (.CONVERT op) effect ∧ finish=n := by
  obtain ⟨g,hg,_⟩ := ConstructiveBodyConversionGeneration.original c stack op effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (ConstructiveBodyConversionGeneration.all c stack env)
    (ConstructiveBodyConversionGeneration.production c stack env g) _ effect n finish _ _ h
  · exact List.mem_map.mpr ⟨g,ConstructiveBodyConversionGeneration.mem_groups g,rfl⟩
  · unfold ConstructiveBodyConversionGeneration.production
    apply ConstructiveBodyPayloadCoverage.mapped (a:=(⟨op,ConstructiveBodyConversionGeneration.valid g op hg⟩ : {v : cvtop_ // ConstructiveBodyConversionTypes.typeOf v=some (ConstructiveBodyConversionGeneration.types g)}))
    exact ConstructiveBodyConversionGeneration.payloads_complete g op hg

theorem vectorBinary (c : context) (stack : inferresulttype) (env : Env c) (op : vbinop_) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.BINARY» op)⟩) n (.success (.of effect)) finish) :
    Covers [ConstructiveBodyVectorBinaryGeneration.production c stack env] (.«VEC.BINARY» op) effect ∧ finish=n := by
  obtain ⟨hl,_⟩ := ConstructiveBodyVectorBinaryGeneration.original c stack op effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack [ConstructiveBodyVectorBinaryGeneration.production c stack env]
    (ConstructiveBodyVectorBinaryGeneration.production c stack env) _ effect n finish (List.mem_singleton_self _) _ h
  unfold ConstructiveBodyVectorBinaryGeneration.production
  apply ConstructiveBodyPayloadCoverage.mapped (a:=(⟨op,hl⟩ : {v : vbinop_ // ConstructiveBodyVectorBinaryRules.legal v=true}))
  exact ConstructiveBodyVectorBinaryGeneration.payloads_complete op hl

theorem extract (c : context) (stack : inferresulttype) (env : Env c) (op : vextractop_) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.EXTRACT» op)⟩) n (.success (.of effect)) finish) :
    Covers (ConstructiveBodyVectorLaneGeneration.all c stack env) (.«VEC.EXTRACT» op) effect ∧ finish=n := by
  obtain ⟨hl,_⟩ := ConstructiveBodyVectorLaneCalls.extract_original c stack op effect n finish h
  obtain ⟨lane,v,hv,he⟩ := ConstructiveBodyVectorLaneGeneration.extract_complete op hl
  apply ConstructiveBodyFunctionCoverage.from_production c stack (ConstructiveBodyVectorLaneGeneration.all c stack env)
    (ConstructiveBodyVectorLaneGeneration.extractProduction c stack env lane) _ effect n finish _ _ h
  · apply List.mem_flatMap.mpr
    refine ⟨lane,ConstructiveBodyVectorLaneGeneration.mem_lanes lane,?_⟩
    simp
  · rw [←he]
    unfold ConstructiveBodyVectorLaneGeneration.extractProduction
    apply ConstructiveBodyPayloadCoverage.mapped (a:=v)
    exact hv

theorem replace (c : context) (stack : inferresulttype) (env : Env c) (op : vreplaceop_) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«VEC.REPLACE» op)⟩) n (.success (.of effect)) finish) :
    Covers (ConstructiveBodyVectorLaneGeneration.all c stack env) (.«VEC.REPLACE» op) effect ∧ finish=n := by
  obtain ⟨hl,_⟩ := ConstructiveBodyVectorLaneCalls.replace_original c stack op effect n finish h
  obtain ⟨lane,v,hv,he⟩ := ConstructiveBodyVectorLaneGeneration.replace_complete op hl
  apply ConstructiveBodyFunctionCoverage.from_production c stack (ConstructiveBodyVectorLaneGeneration.all c stack env)
    (ConstructiveBodyVectorLaneGeneration.replaceProduction c stack env lane) _ effect n finish _ _ h
  · apply List.mem_flatMap.mpr
    refine ⟨lane,ConstructiveBodyVectorLaneGeneration.mem_lanes lane,?_⟩
    simp
  · rw [←he]
    unfold ConstructiveBodyVectorLaneGeneration.replaceProduction
    apply ConstructiveBodyPayloadCoverage.mapped (a:=v)
    exact hv

#print axioms unary
#print axioms conversion
#print axioms vectorBinary
#print axioms extract
#print axioms replace
end properties.wasm_module_ok.ConstructiveBodyRestrictedCoverage
