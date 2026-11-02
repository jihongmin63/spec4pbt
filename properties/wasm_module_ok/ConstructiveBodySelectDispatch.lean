import properties.wasm_module_ok.ConstructiveBodyTypeClassifiers
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodySelectDispatch
open SpecTec properties.wasm_module_ok

theorem original_cases (c : context) (stack : inferresulttype) (ts : Option (List valtype)) (effect : inferinstrtype)
    (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.SELECT ts)⟩) n (.success (.of effect)) finish) :
    SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:3» c stack (.SELECT ts)) n (.success (.of effect)) finish ∨
    SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:4» c stack (.SELECT ts)) n (.success (.of effect)) finish := by
  cases h with | call h =>
   change SpecTecExecution.Eval SpecTec.Body
     (SpecTecExecution.tryClauses (SpecTec.Instr_ok_clauses c stack (.SELECT ts))) n _ finish at h
   obtain ⟨j,hs⟩ := (SpecTecExecution.tryClauses_success_iff _ _ _ _).1 h
   obtain ⟨hj,he⟩ := ConstructiveBodyRoute.selected_get _ n finish j (.of effect) hs
   have ho : ConstructiveBodyOpcode.ruleOpcode j=3 := by
     by_contra hn
     have hm := ConstructiveBodyOpcode.other c stack (.SELECT ts) n j hj (by simpa [instr.ctorIdx] using Ne.symm hn)
     have hc := (properties.wasm_module_ok.Execution.eval_deterministic he hm).1
     cases hc
   have which : ∀k : Fin 100,ConstructiveBodyOpcode.ruleOpcode k.val=3 → k.val=3 ∨ k.val=4 := by decide
   rcases which ⟨j,hj⟩ ho with heq|heq
   · change j=3 at heq
     subst j
     exact Or.inl he
   · change j=4 at heq
     subst j
     exact Or.inr he

theorem none_clause (c : context) (stack : inferresulttype) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.SELECT none)⟩) n (.success (.of effect)) finish) :
    SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:3» c stack (.SELECT none)) n (.success (.of effect)) finish := by
  rcases original_cases c stack none effect n finish h with h|h
  · exact h
  · unfold SpecTec.«Instr_ok:clause:4» at h
    cases h with | bind_success hg tail =>
     cases hg
     cases tail with | bind_success hg _ =>
      cases hg with | guard_true hc => cases hc

theorem some_clause (c : context) (stack : inferresulttype) (ts : List valtype) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.SELECT (some ts))⟩) n (.success (.of effect)) finish) :
    SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:4» c stack (.SELECT (some ts))) n (.success (.of effect)) finish := by
  rcases original_cases c stack (some ts) effect n finish h with h|h
  · unfold SpecTec.«Instr_ok:clause:3» at h
    cases h with | bind_success hg _ =>
     cases hg with | guard_true hc => cases hc
  · exact h

theorem none_forward (c : context) (stack : inferresulttype) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:3» c stack (.SELECT none)) n (.success (.of effect)) finish) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.SELECT none)⟩) n (.success (.of effect)) finish := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Instr_ok_clauses c stack (.SELECT none))) n _ finish
  apply ConstructiveBodyRoute.first_at _ 3 (by change 3<100; decide) n finish (.of effect) h
  intro j hj
  have hd : j=0 ∨ j=1 ∨ j=2 := by omega
  rcases hd with rfl|rfl|rfl
  · exact ConstructiveBodyOpcode.other0 c stack _ n (by simp [instr.ctorIdx])
  · exact ConstructiveBodyOpcode.other1 c stack _ n (by simp [instr.ctorIdx])
  · exact ConstructiveBodyOpcode.other2 c stack _ n (by simp [instr.ctorIdx])

theorem some_forward (c : context) (stack : inferresulttype) (ts : List valtype) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body (SpecTec.«Instr_ok:clause:4» c stack (.SELECT (some ts))) n (.success (.of effect)) finish) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.SELECT (some ts))⟩) n (.success (.of effect)) finish := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Instr_ok_clauses c stack (.SELECT (some ts)))) n _ finish
  apply ConstructiveBodyRoute.first_at _ 4 (by change 4<100; decide) n finish (.of effect) h
  intro j hj
  have hd : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases hd with rfl|rfl|rfl|rfl
  · exact ConstructiveBodyOpcode.other0 c stack _ n (by simp [instr.ctorIdx])
  · exact ConstructiveBodyOpcode.other1 c stack _ n (by simp [instr.ctorIdx])
  · exact ConstructiveBodyOpcode.other2 c stack _ n (by simp [instr.ctorIdx])
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))

#print axioms original_cases
#print axioms some_forward
end properties.wasm_module_ok.ConstructiveBodySelectDispatch
