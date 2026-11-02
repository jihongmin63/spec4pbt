import properties.wasm_module_ok.ConstructiveBodyReferenceMembers
import properties.wasm_module_ok.ConstructiveBodyReferenceOriginal
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyReferenceProductions ConstructiveBodyProductionCoverage

theorem nullRef_original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (heap : heaptype) (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.NULL» heap)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.«REF.NULL» heap) effect ∧ finish=n := by
  have hv := (ConstRefNullDispatch.ref_null_dispatch_iff c stack heap effect n finish).1 h |>.1
  have hh := (FiniteValidTypes.heapCandidates_spec c heap).2 hv
  exact ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs) (nullRef c stack env heap hh) _ effect n finish
    (ConstructiveBodyReferenceMembers.nullRef_mem c stack env hs heap hh)
    (ConstructiveBodyReferenceMembers.nullRef_produces c stack env heap hh) h

theorem funcRef_original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (x : Nat) (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.FUNC» x)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.«REF.FUNC» x) effect ∧ finish=n := by
  obtain ⟨dt,hx,hr,_,_⟩ := (ConstRefFuncEffect.ref_func_instruction_iff c stack x effect n finish).1 h
  let e : ConstructiveBodyLookup.Entry c.FUNCS := ⟨x,dt,hx⟩
  exact ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs) (funcRef c stack env e hr) _ effect n finish
    (ConstructiveBodyReferenceMembers.funcRef_mem c stack env hs e hr)
    (ConstructiveBodyReferenceMembers.funcRef_produces c stack env e hr) h

theorem equal_original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.EQ»)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.«REF.EQ») effect ∧ finish=n := by
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs) (equal c stack env) _ effect n finish
    (ConstructiveBodyReferenceMembers.static_mem c stack env hs _ ?_) (ConstructiveBodyReferenceMembers.equal_produces c stack env) h
  simp

theorem i31_original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.I31»)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.«REF.I31») effect ∧ finish=n := by
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs) (i31 c stack env) _ effect n finish
    (ConstructiveBodyReferenceMembers.static_mem c stack env hs _ ?_) (ConstructiveBodyReferenceMembers.i31_produces c stack env) h
  simp

theorem getI31_original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (extension : SpecTec.extension) (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«I31.GET» extension)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.«I31.GET» extension) effect ∧ finish=n := by
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs) (getI31 c stack env extension) _ effect n finish
    (ConstructiveBodyReferenceMembers.static_mem c stack env hs _ ?_) (ConstructiveBodyReferenceMembers.getI31_produces c stack env extension) h
  cases extension <;> simp

theorem arrayLength_original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«ARRAY.LEN»)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.«ARRAY.LEN») effect ∧ finish=n := by
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs) (arrayLength c stack env) _ effect n finish
    (ConstructiveBodyReferenceMembers.static_mem c stack env hs _ ?_) (ConstructiveBodyReferenceMembers.arrayLength_produces c stack env) h
  simp

theorem isNull_original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.IS_NULL»)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.«REF.IS_NULL») effect ∧ finish=n := by
  obtain ⟨nu,heap,hp⟩ := ConstructiveBodyReferenceOriginal.isNull c stack effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs) (isNull c stack env hs nu heap hp) _ effect n finish
    (ConstructiveBodyReferenceMembers.peek_mem c stack env hs nu heap hp _ ?_) (ConstructiveBodyReferenceMembers.isNull_produces c stack env hs nu heap hp) h
  simp

theorem asNonNull_original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.AS_NON_NULL»)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.«REF.AS_NON_NULL») effect ∧ finish=n := by
  obtain ⟨nu,heap,hp⟩ := ConstructiveBodyReferenceOriginal.asNonNull c stack effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs) (asNonNull c stack env hs nu heap hp) _ effect n finish
    (ConstructiveBodyReferenceMembers.peek_mem c stack env hs nu heap hp _ ?_) (ConstructiveBodyReferenceMembers.asNonNull_produces c stack env hs nu heap hp) h
  simp

theorem externConvert_original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (op : externop_) (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«EXTERN.CONVERT» op)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.«EXTERN.CONVERT» op) effect ∧ finish=n := by
  obtain ⟨nu,heap,hp⟩ := ConstructiveBodyReferenceOriginal.externConvert c stack op effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs) (externConvert c stack env op nu heap hp) _ effect n finish
    (ConstructiveBodyReferenceMembers.peek_mem c stack env hs nu heap hp _ ?_) (ConstructiveBodyReferenceMembers.externConvert_produces c stack env op nu heap hp) h
  cases op <;> simp

#print axioms nullRef_original
#print axioms externConvert_original
end properties.wasm_module_ok.ConstructiveBodyReferenceCoverage
