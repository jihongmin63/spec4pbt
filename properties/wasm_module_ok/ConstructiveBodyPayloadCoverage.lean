import properties.wasm_module_ok.ConstructiveBodyNumericAtoms
import properties.wasm_module_ok.ConstructiveBodyOperatorProductions
import properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyPayloadCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyProductionCoverage ConstructiveConstTableCore

theorem mapped {α : Type} (c : context) (stack : inferresulttype) (env : Env c)
    (ins outs : List valtype) (hi : ∀t∈ins,ConstructiveBodyOperatorProductions.Plain t) (ho : ∀t∈outs,ConstructiveBodyOperatorProductions.Plain t)
    (g : Audited α) (make : α → instr)
    (sound : ∀a n,SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (make a)⟩)
      n (.success (.of (ConstructiveBodyControl.effect ins outs []))) n)
    (a : α) (ha : Gen.support g.generator a) :
    Produces (ConstructiveBodyOperatorProductions.production c stack env ins outs hi ho g make sound) (make a) := by
  refine ⟨⟨make a,sound a⟩,?_,rfl⟩
  exact ⟨a,ha,rfl⟩

theorem numericPayloads (v : num_) :
    Gen.support (ConstructiveBodyNumericAtoms.payloads (ConstLiteralEffect.numericType v)).generator ⟨v,rfl⟩ := by
  cases v with
  | I32 n => exact ⟨n,by simp,rfl⟩
  | I64 n => exact ⟨n,by simp,rfl⟩
  | F32 f => exact ⟨f,ConstructiveConstLiteralGen.floats32_support f,rfl⟩
  | F64 f => exact ⟨f,ConstructiveConstLiteralGen.floats64_support f,rfl⟩

theorem numeric (c : context) (stack : inferresulttype) (env : Env c) (v : num_) :
    ∃p∈ConstructiveBodyNumericAtoms.literals c stack env,Produces p (.CONST v) := by
  refine ⟨ConstructiveBodyNumericAtoms.numbers c stack env (ConstLiteralEffect.numericType v),?_,?_⟩
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨_,by cases v <;> simp [ConstLiteralEffect.numericType],rfl⟩
  · unfold Produces ConstructiveBodyNumericAtoms.numbers ConstructiveBodySimpleAtoms.unchanged
    refine ⟨_,⟨⟨v,rfl⟩,numericPayloads v,rfl⟩,rfl⟩

theorem vector (c : context) (stack : inferresulttype) (env : Env c) (v : vec_) :
    ∃p∈ConstructiveBodyNumericAtoms.literals c stack env,Produces p (.«VEC.CONST» v) := by
  refine ⟨ConstructiveBodyNumericAtoms.vectors c stack env,?_,?_⟩
  · exact List.mem_append_right _ (List.mem_singleton_self _)
  · cases v with | V128 n =>
      unfold Produces ConstructiveBodyNumericAtoms.vectors ConstructiveBodySimpleAtoms.unchanged
      exact ⟨_,⟨n,by simp,rfl⟩,rfl⟩

theorem unreachable (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) :
    ∃p∈ConstructiveBodySimpleAtoms.plain c stack env hs,Produces p .UNREACHABLE := by
  let p := (ConstructiveBodySimpleAtoms.plain c stack env hs)[0]'(by simp [ConstructiveBodySimpleAtoms.plain])
  refine ⟨p,List.getElem_mem _,?_⟩
  exact ⟨_,rfl,rfl⟩

theorem nop (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) :
    ∃p∈ConstructiveBodySimpleAtoms.plain c stack env hs,Produces p .NOP := by
  let p := (ConstructiveBodySimpleAtoms.plain c stack env hs)[1]'(by simp [ConstructiveBodySimpleAtoms.plain])
  refine ⟨p,List.getElem_mem _,?_⟩
  exact ⟨_,rfl,rfl⟩

theorem drop (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) :
    ∃p∈ConstructiveBodySimpleAtoms.plain c stack env hs,Produces p .DROP := by
  let p := (ConstructiveBodySimpleAtoms.plain c stack env hs)[2]'(by simp [ConstructiveBodySimpleAtoms.plain])
  refine ⟨p,List.getElem_mem _,?_⟩
  exact ⟨_,rfl,rfl⟩

theorem returnValue (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) :
    ∃p∈ConstructiveBodySimpleAtoms.plain c stack env hs,Produces p .RETURN := by
  let p := (ConstructiveBodySimpleAtoms.plain c stack env hs)[3]'(by simp [ConstructiveBodySimpleAtoms.plain])
  refine ⟨p,List.getElem_mem _,?_⟩
  exact ⟨_,rfl,rfl⟩

theorem throwRef (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack) :
    ∃p∈ConstructiveBodySimpleAtoms.plain c stack env hs,Produces p .THROW_REF := by
  let p := (ConstructiveBodySimpleAtoms.plain c stack env hs)[4]'(by simp [ConstructiveBodySimpleAtoms.plain])
  refine ⟨p,List.getElem_mem _,?_⟩
  exact ⟨_,rfl,rfl⟩

#print axioms numeric
#print axioms unreachable
end properties.wasm_module_ok.ConstructiveBodyPayloadCoverage
