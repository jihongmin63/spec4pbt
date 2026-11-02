import properties.wasm_module_ok.ConstructiveBodyStorageMetadata
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyGetDispatch
open SpecTec properties.wasm_module_ok SpecTecExecution

theorem pair_rule (c : context) (stack : inferresulttype) (i : instr) (k other : Fin 100)
    (hi : i.ctorIdx=ConstructiveBodyOpcode.ruleOpcode k.val)
    (hu : ∀j : Fin 100,ConstructiveBodyOpcode.ruleOpcode j.val=ConstructiveBodyOpcode.ruleOpcode k.val → j=k ∨ j=other)
    (hm : ∀n,Eval SpecTec.Body (((SpecTec.Instr_ok_clauses c stack i)[other.val]'other.isLt)) n .unmatch n)
    (effect : inferinstrtype) (n finish : Nat) :
    Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack i⟩) n (.success (.of effect)) finish ↔
    Eval SpecTec.Body (((SpecTec.Instr_ok_clauses c stack i)[k.val]'k.isLt)) n (.success (.of effect)) finish := by
  constructor
  · intro h
    cases h with | call h =>
      change Eval SpecTec.Body (tryClauses (SpecTec.Instr_ok_clauses c stack i)) n _ finish at h
      obtain ⟨j,hs⟩ := (properties.wasm_module_ok.Execution.tryClauses_success_iff _ _ _ _).1 h
      obtain ⟨hj,he⟩ := ConstructiveBodyRoute.selected_get _ n finish j (.of effect) hs
      have ho : i.ctorIdx=ConstructiveBodyOpcode.ruleOpcode j := by
        by_contra hn
        have hx := ConstructiveBodyOpcode.other c stack i n j hj hn
        cases (properties.wasm_module_ok.Execution.eval_deterministic he hx
          (Execution.plain_clause ⟨_,Call.Instr_ok c stack i⟩ (List.getElem_mem _))).1
      rcases hu ⟨j,hj⟩ (ho.symm.trans hi) with eqk|eqother
      · have hjk := congrArg Fin.val eqk
        change j=k.val at hjk
        subst j; exact he
      · have hjo := congrArg Fin.val eqother
        change j=other.val at hjo
        subst j
        cases (properties.wasm_module_ok.Execution.eval_deterministic he (hm n)
          (Execution.plain_clause ⟨_,Call.Instr_ok c stack i⟩ (List.getElem_mem _))).1
  · intro h
    apply Eval.call
    change Eval SpecTec.Body (tryClauses (SpecTec.Instr_ok_clauses c stack i)) n _ finish
    apply ConstructiveBodyRoute.first_at (SpecTec.Instr_ok_clauses c stack i) k.val k.isLt n finish (.of effect) h
    intro j hj
    by_cases he : j=other.val
    · subst j; exact hm n
    · apply ConstructiveBodyOpcode.other c stack i n j (by omega)
      intro ho
      rcases hu ⟨j,by omega⟩ (ho.symm.trans hi) with hk|hn
      · have hv:=congrArg Fin.val hk; change j=k.val at hv; omega
      · exact he (congrArg Fin.val hn)

theorem structSome (c : context) (stack : inferresulttype) (x y : Nat) (ext : extension) (effect : inferinstrtype) (n finish : Nat) :
    Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«STRUCT.GET» x y (some ext))⟩) n (.success (.of effect)) finish ↔
    Eval SpecTec.Body (SpecTec.«Instr_ok:clause:61» c stack (.«STRUCT.GET» x y (some ext))) n (.success (.of effect)) finish := by
  apply pair_rule c stack (.«STRUCT.GET» x y (some ext)) ⟨61,by decide⟩ ⟨62,by decide⟩ rfl (by decide) _ effect n finish
  intro start
  change Eval SpecTec.Body (SpecTec.«Instr_ok:clause:62» c stack (.«STRUCT.GET» x y (some ext))) start .unmatch start
  unfold SpecTec.«Instr_ok:clause:62»
  apply Eval.bind_success (Eval.guard_true rfl)
  exact Eval.bind_unmatch (Eval.guard_false (by change ¬false=true; decide))

theorem structNone (c : context) (stack : inferresulttype) (x y : Nat) (effect : inferinstrtype) (n finish : Nat) :
    Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«STRUCT.GET» x y none)⟩) n (.success (.of effect)) finish ↔
    Eval SpecTec.Body (SpecTec.«Instr_ok:clause:62» c stack (.«STRUCT.GET» x y none)) n (.success (.of effect)) finish := by
  apply pair_rule c stack (.«STRUCT.GET» x y none) ⟨62,by decide⟩ ⟨61,by decide⟩ rfl (by decide) _ effect n finish
  intro start
  change Eval SpecTec.Body (SpecTec.«Instr_ok:clause:61» c stack (.«STRUCT.GET» x y none)) start .unmatch start
  unfold SpecTec.«Instr_ok:clause:61»
  apply Eval.bind_success (Eval.guard_true rfl)
  exact Eval.bind_unmatch (Eval.guard_false (by change ¬false=true; decide))

theorem arraySome (c : context) (stack : inferresulttype) (x : Nat) (ext : extension) (effect : inferinstrtype) (n finish : Nat) :
    Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«ARRAY.GET» x (some ext))⟩) n (.success (.of effect)) finish ↔
    Eval SpecTec.Body (SpecTec.«Instr_ok:clause:69» c stack (.«ARRAY.GET» x (some ext))) n (.success (.of effect)) finish := by
  apply pair_rule c stack (.«ARRAY.GET» x (some ext)) ⟨69,by decide⟩ ⟨70,by decide⟩ rfl (by decide) _ effect n finish
  intro start
  change Eval SpecTec.Body (SpecTec.«Instr_ok:clause:70» c stack (.«ARRAY.GET» x (some ext))) start .unmatch start
  unfold SpecTec.«Instr_ok:clause:70»
  apply Eval.bind_success (Eval.guard_true rfl)
  exact Eval.bind_unmatch (Eval.guard_false (by change ¬false=true; decide))

theorem arrayNone (c : context) (stack : inferresulttype) (x : Nat) (effect : inferinstrtype) (n finish : Nat) :
    Eval SpecTec.Body (.call ⟨inferinstrtype,Call.Instr_ok c stack (.«ARRAY.GET» x none)⟩) n (.success (.of effect)) finish ↔
    Eval SpecTec.Body (SpecTec.«Instr_ok:clause:70» c stack (.«ARRAY.GET» x none)) n (.success (.of effect)) finish := by
  apply pair_rule c stack (.«ARRAY.GET» x none) ⟨70,by decide⟩ ⟨69,by decide⟩ rfl (by decide) _ effect n finish
  intro start
  change Eval SpecTec.Body (SpecTec.«Instr_ok:clause:69» c stack (.«ARRAY.GET» x none)) start .unmatch start
  unfold SpecTec.«Instr_ok:clause:69»
  apply Eval.bind_success (Eval.guard_true rfl)
  exact Eval.bind_unmatch (Eval.guard_false (by change ¬false=true; decide))

#print axioms arrayNone
end properties.wasm_module_ok.ConstructiveBodyGetDispatch
