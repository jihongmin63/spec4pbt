import properties.wasm_module_ok.ConstructiveBodySelectDispatch
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodySelectCalls
open SpecTec properties.wasm_module_ok ConstructiveBodyTypeClassifiers

def plainType (stack : inferresulttype) : valtype := PeekDecision.peekResult 1 stack
def plainAllowed (stack : inferresulttype) : Bool := numeric (plainType stack) || vector (plainType stack)

theorem plain (c : context) (stack : inferresulttype) (hp : plainAllowed stack=true) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.SELECT none)⟩)
      n (.success (.of (ConstructiveBodyControl.effect [plainType stack,plainType stack,.NumT .I32T] [plainType stack] []))) n := by
  apply ConstructiveBodySelectDispatch.none_forward
  unfold SpecTec.«Instr_ok:clause:3»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (PeekDecision.peek_total 1 stack n)
  apply SpecTecExecution.Eval.bind_success (numeric_total (plainType stack) n)
  apply SpecTecExecution.Eval.bind_success (vector_total (plainType stack) n)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (Bool.or_eq_true_iff.mp hp))
  exact SpecTecExecution.Eval.pure _

theorem typed (c : context) (stack : inferresulttype) (t : valtype) (ht : ValtypeValidation.valtypeValid c t=true) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.SELECT (some [t]))⟩)
      n (.success (.of (ConstructiveBodyControl.effect [t,t,.NumT .I32T] [t] []))) n := by
  apply ConstructiveBodySelectDispatch.some_forward
  unfold SpecTec.«Instr_ok:clause:4»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success ((FunctypeValidation.resulttype_success_iff_valid c [t] n n).2
    ⟨by simp [FunctypeValidation.resulttypeValid,ResulttypeListValidation.allValtypesValid,ht],rfl⟩)
  exact SpecTecExecution.Eval.pure _

#print axioms plain
#print axioms typed
end properties.wasm_module_ok.ConstructiveBodySelectCalls
