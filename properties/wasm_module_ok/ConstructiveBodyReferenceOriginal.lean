import properties.wasm_module_ok.ConstructiveBodyReferenceProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceOriginal
open SpecTec properties.wasm_module_ok

theorem isNull (c : context) (stack : inferresulttype) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack .«REF.IS_NULL»⟩) n (.success (.of effect)) finish) :
    ∃(nu : SpecTec.null) (heap : heaptype),
      PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap) := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack .«REF.IS_NULL» 52 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:52» c stack .«REF.IS_NULL») n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:52» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hp tail =>
    rename_i mid rt
    cases rt with | «% %» nu heap =>
     exact ⟨nu,heap,(PeekRefDecision.peek_ref_success_iff_result 0 stack _ _ _).1 hp |>.1⟩

theorem asNonNull (c : context) (stack : inferresulttype) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack .«REF.AS_NON_NULL»⟩) n (.success (.of effect)) finish) :
    ∃(nu : SpecTec.null) (heap : heaptype),
      PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap) := by
  have hs := (ConstructiveBodyRoute.unique_rule c stack .«REF.AS_NON_NULL» 53 (by decide) rfl (by decide) effect n finish).1 h
  change SpecTecExecution.Eval SpecTec.specTecProgram (SpecTec.«Instr_ok:clause:53» c stack .«REF.AS_NON_NULL») n _ finish at hs
  unfold SpecTec.«Instr_ok:clause:53» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hp tail =>
    rename_i mid rt
    cases rt with | «% %» nu heap =>
     exact ⟨nu,heap,(PeekRefDecision.peek_ref_success_iff_result 0 stack _ _ _).1 hp |>.1⟩

theorem externConvert (c : context) (stack : inferresulttype) (op : externop_) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack (.«EXTERN.CONVERT» op)⟩) n (.success (.of effect)) finish) :
    ∃(nu : SpecTec.null) (heap : heaptype),
      PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap) := by
  have hr := (ConstExternConvertDecision.extern_convert_success_iff_result c stack op effect n finish).1 h |>.1
  cases hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack) with
  | none => simp [ConstExternConvertDecision.externConvertResult,hp] at hr
  | some rt => cases rt with | «% %» nu heap => exact ⟨nu,heap,rfl⟩

#print axioms isNull
#print axioms externConvert
end properties.wasm_module_ok.ConstructiveBodyReferenceOriginal
