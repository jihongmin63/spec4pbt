import properties.wasm_module_ok.ConstructiveBodySelectDispatch
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodySelectOriginal
open SpecTec properties.wasm_module_ok ConstructiveBodyTypeClassifiers

private theorem bool_exact (call : Call Bool) (expected actual : Bool) (n finish : Nat)
    (ht : SpecTecExecution.Eval SpecTec.Body (.call ⟨Bool,call⟩) n (.success (.of expected)) n)
    (ha : SpecTecExecution.Eval SpecTec.Body (.call ⟨Bool,call⟩) n (.success (.of actual)) finish) :
    actual=expected ∧ finish=n := by
  obtain ⟨he,hf⟩ := properties.wasm_module_ok.Execution.eval_deterministic ha ht
  cases he
  exact ⟨rfl,hf⟩

theorem plain (c : context) (stack : inferresulttype) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.SELECT none)⟩) n (.success (.of effect)) finish) :
    numeric (PeekDecision.peekResult 1 stack)=true ∨ vector (PeekDecision.peekResult 1 stack)=true := by
  have hs := ConstructiveBodySelectDispatch.none_clause c stack effect n finish h
  unfold SpecTec.«Instr_ok:clause:3» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hp tail =>
    obtain ⟨he,_⟩ := (PeekDecision.peek_success_iff_result 1 stack _ _ _).1 hp
    rw [he] at tail
    cases tail with | bind_success hn tail =>
     obtain ⟨he,_⟩ := bool_exact _ _ _ _ _ (numeric_total _ _) hn
     rw [he] at tail
     cases tail with | bind_success hv tail =>
      obtain ⟨he,_⟩ := bool_exact _ _ _ _ _ (vector_total _ _) hv
      rw [he] at tail
      cases tail with | bind_success hg _ =>
       cases hg with | guard_true hc => exact hc

theorem typed (c : context) (stack : inferresulttype) (ts : List valtype) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.SELECT (some ts))⟩) n (.success (.of effect)) finish) :
    ∃t,ts=[t] ∧ ValtypeValidation.valtypeValid c t=true := by
  have hs := ConstructiveBodySelectDispatch.some_clause c stack ts effect n finish h
  unfold SpecTec.«Instr_ok:clause:4» at hs
  cases hs with | bind_success hg tail =>
   cases hg
   cases tail with | bind_success hg tail =>
    cases hg
    cases tail with | bind_success hl tail =>
     cases hl with | guard_true hl =>
      obtain ⟨t,he⟩ := List.length_eq_one_iff.mp hl.symm
      subst ts
      cases tail with | bind_success hv _ =>
       have hv := (FunctypeValidation.resulttype_success_iff_valid c [t] _ _).1 hv |>.1
       exact ⟨t,rfl,by simpa [FunctypeValidation.resulttypeValid,ResulttypeListValidation.allValtypesValid] using hv⟩

#print axioms plain
#print axioms typed
end properties.wasm_module_ok.ConstructiveBodySelectOriginal
