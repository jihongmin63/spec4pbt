import properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
import properties.wasm_module_ok.ConstExternConvertDecision
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceCalls
open SpecTec properties.wasm_module_ok

theorem equal (c : context) (stack : inferresulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.EQ»)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null .EqHT),.RefT (.«% %» .Null .EqHT)] [.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«REF.EQ») 56 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:56» c stack (.«REF.EQ»)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:56»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

theorem getI31 (c : context) (stack : inferresulttype) (extension : SpecTec.extension) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«I31.GET» extension)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null .I31HT)] [.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«I31.GET» extension) 58 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:58» c stack (.«I31.GET» extension)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:58»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

theorem arrayLength (c : context) (stack : inferresulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«ARRAY.LEN»)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null .ArrayHT)] [.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«ARRAY.LEN») 72 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:72» c stack (.«ARRAY.LEN»)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:72»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  exact SpecTecExecution.Eval.pure _

theorem isNull (c : context) (stack : inferresulttype) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.IS_NULL»)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null heap)] [.NumT .I32T] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«REF.IS_NULL») 52 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:52» c stack (.«REF.IS_NULL»)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:52»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (PeekRefDecision.peek_ref_total_of_some 0 stack (.«% %» nu heap) n hp)
  exact SpecTecExecution.Eval.pure _

theorem asNonNull (c : context) (stack : inferresulttype) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«REF.AS_NON_NULL»)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [.RefT (.«% %» .Null heap)] [.RefT (.«% %» .NoNull heap)] []))) n := by
  apply (ConstructiveBodyRoute.unique_rule c stack (.«REF.AS_NON_NULL») 53 (by decide) rfl (by decide) _ n n).2
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:53» c stack (.«REF.AS_NON_NULL»)) n (.success (.of _)) n
  unfold SpecTec.«Instr_ok:clause:53»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (PeekRefDecision.peek_ref_total_of_some 0 stack (.«% %» nu heap) n hp)
  exact SpecTecExecution.Eval.pure _

theorem externConvert (c : context) (stack : inferresulttype) (op : externop_) (nu : SpecTec.null) (heap : heaptype)
    (hp : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 stack)=some (.«% %» nu heap)) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«EXTERN.CONVERT» op)⟩)
      n (.success (.of (ConstructiveBodyControl.effect
        [.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1)]
        [.RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).2)] []))) n := by
  apply (ConstExternConvertDecision.extern_convert_success_iff_result c stack op _ n n).2
  exact ⟨by simp only [ConstExternConvertDecision.externConvertResult,hp]; rfl,rfl⟩

#print axioms externConvert
#print axioms asNonNull
end properties.wasm_module_ok.ConstructiveBodyReferenceCalls
