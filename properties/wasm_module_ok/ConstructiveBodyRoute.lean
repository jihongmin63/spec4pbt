import properties.wasm_module_ok.ConstructiveBodyOpcode
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyRoute
open SpecTec properties.wasm_module_ok
private theorem deterministic : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
  intro request a b h; cases h

theorem selected_get (clauses : List (SpecTecExecution.Clause SpecTecRequest Unit))
    (start finish k : Nat) (value : SpecTecExecution.Value)
    (h : SpecTecExecution.Selected SpecTec.specTecProgram () clauses start k value finish) :
    ∃hk : k<clauses.length,SpecTecExecution.Eval SpecTec.specTecProgram
      (clauses[k] ()) start (.success value) finish := by
  induction h with
  | here h => exact ⟨by simp,h⟩
  | next _ _ ih =>
    obtain ⟨hk,he⟩ := ih
    exact ⟨by simpa using Nat.succ_lt_succ hk,by simpa using he⟩

theorem first_at (clauses : List (SpecTecExecution.Clause SpecTecRequest Unit))
    (k : Nat) (hk : k<clauses.length) (start finish : Nat) (value : SpecTecExecution.Value)
    (he : SpecTecExecution.Eval SpecTec.specTecProgram (clauses[k] ()) start (.success value) finish)
    (hp : ∀j,(hj : j<k) → SpecTecExecution.Eval SpecTec.specTecProgram
      ((clauses[j]'(Nat.lt_trans hj hk)) ()) start .unmatch start) :
    SpecTecExecution.Eval SpecTec.specTecProgram (SpecTecExecution.firstSuccess clauses ())
      start (.success value) finish := by
  induction clauses generalizing k with
  | nil => simp at hk
  | cons h t ih =>
    cases k with
    | zero => exact SpecTecExecution.firstSuccess_cons_success he
    | succ k =>
      apply SpecTecExecution.firstSuccess_cons_unmatch (hp 0 (by omega))
      exact ih k (by simpa using hk) he (by intro j hj; exact hp (j+1) (by omega))

/-- All earlier original clauses normally unmatch; aborts are never skipped. -/
theorem unique_rule (c : context) (stack : inferresulttype) (i : instr)
    (k : Nat) (hk : k<100) (hi : i.ctorIdx=ConstructiveBodyOpcode.ruleOpcode k)
    (hu : ∀j : Fin 100,ConstructiveBodyOpcode.ruleOpcode j.val=ConstructiveBodyOpcode.ruleOpcode k → j.val=k)
    (result : inferinstrtype) (start finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack i⟩)
      start (.success (.of result)) finish ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (((SpecTec.Instr_ok_clauses c stack i)[k]'(by exact hk)) ())
      start (.success (.of result)) finish := by
  constructor
  · intro h
    cases h with | call h =>
     change SpecTecExecution.Eval SpecTec.specTecProgram
       (SpecTecExecution.firstSuccess (SpecTec.Instr_ok_clauses c stack i) ())
       start (.success (.of result)) finish at h
     obtain ⟨j,hs⟩ := (SpecTecExecution.firstSuccess_success_iff _ _ _ _ _).1 h
     obtain ⟨hj,he⟩ := selected_get _ start finish j (.of result) hs
     have hj' : j<100 := hj
     have ho : i.ctorIdx=ConstructiveBodyOpcode.ruleOpcode j := by
       by_contra hn
       have hm := ConstructiveBodyOpcode.other c stack i start j hj' hn
       have hc := (SpecTecExecution.eval_deterministic deterministic he hm).1
       cases hc
     have hjk := hu ⟨j,hj'⟩ (ho.symm.trans hi)
     change j=k at hjk
     subst j
     exact he
  · intro h
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Instr_ok_clauses c stack i) ())
      start (.success (.of result)) finish
    apply first_at _ k (by exact hk) start finish (.of result) h
    intro j hj
    apply ConstructiveBodyOpcode.other c stack i start j (by omega)
    intro ho
    have hjk := hu ⟨j,by omega⟩ (ho.symm.trans hi)
    change j=k at hjk
    omega

#print axioms unique_rule
end properties.wasm_module_ok.ConstructiveBodyRoute
