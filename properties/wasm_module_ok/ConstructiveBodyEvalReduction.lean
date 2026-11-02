import properties.wasm_module_ok.ConstructiveBodyMemoryCalls
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyEvalReduction
open SpecTec properties.wasm_module_ok SpecTecExecution

theorem deterministic : PrimitiveDeterministic SpecTec.specTecProgram := by intro request a b h; cases h

theorem bind_known {α : Type} (p : Plan SpecTecRequest) (k : α → Plan SpecTecRequest)
    (x : α) (n finish : Nat) (out : Outcome Value)
    (hp : Eval SpecTec.specTecProgram p n (.success (.of x)) n) :
    Eval SpecTec.specTecProgram (.bind p k) n out finish ↔
    Eval SpecTec.specTecProgram (k x) n out finish := by
  constructor
  · intro h
    cases h with
    | bind_success hfirst hrest =>
      obtain ⟨he,hn⟩ := eval_deterministic deterministic hfirst hp
      cases he; cases hn; exact hrest
    | bind_unmatch hfirst => cases (eval_deterministic deterministic hfirst hp).1
    | bind_abort hfirst => cases (eval_deterministic deterministic hfirst hp).1
  · exact Eval.bind_success hp

theorem bind_guard (p : Prop) (k : Unit → Plan SpecTecRequest) (n finish : Nat) (v : Value) :
    Eval SpecTec.specTecProgram (.bind (.guard p) k) n (.success v) finish ↔
    p ∧ Eval SpecTec.specTecProgram (k ()) n (.success v) finish := by
  constructor
  · intro h
    cases h with | bind_success hg hr =>
      cases hg with | guard_true hp => exact ⟨hp,hr⟩
  · rintro ⟨hp,hr⟩; exact Eval.bind_success (Eval.guard_true hp) hr

theorem pure_success {α : Type} (x y : α) (n finish : Nat) :
    Eval SpecTec.specTecProgram (.pure x) n (.success (.of y)) finish ↔ y=x ∧ finish=n := by
  constructor
  · intro h; cases h; exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩; exact Eval.pure _

#print axioms bind_known
end properties.wasm_module_ok.ConstructiveBodyEvalReduction
