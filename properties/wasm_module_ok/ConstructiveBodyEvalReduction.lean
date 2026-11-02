import properties.wasm_module_ok.ConstructiveBodyMemoryCalls
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyEvalReduction
open SpecTec properties.wasm_module_ok SpecTecExecution


theorem bind_known {α : Type} (p : Plan Request) (k : α → Plan Request)
    (x : α) (n finish : Nat) (out : Outcome Value)
    (hp : Eval SpecTec.Body p n (.success (.of x)) n) :
    Eval SpecTec.Body (.bind p k) n out finish ↔
    Eval SpecTec.Body (k x) n out finish := by
  constructor
  · intro h
    cases h with
    | bind_success hfirst hrest =>
      obtain ⟨he,hn⟩ := properties.wasm_module_ok.Execution.eval_deterministic hfirst hp
      cases he; cases hn; exact hrest
    | bind_unmatch hfirst => cases (properties.wasm_module_ok.Execution.eval_deterministic hfirst hp).1
    | bind_abort hfirst => cases (properties.wasm_module_ok.Execution.eval_deterministic hfirst hp).1
  · exact Eval.bind_success hp

theorem bind_guard (p : Prop) (k : Unit → Plan Request) (n finish : Nat) (v : Value) :
    Eval SpecTec.Body (.bind (.guard p) k) n (.success v) finish ↔
    p ∧ Eval SpecTec.Body (k ()) n (.success v) finish := by
  constructor
  · intro h
    cases h with | bind_success hg hr =>
      cases hg with | guard_true hp => exact ⟨hp,hr⟩
  · rintro ⟨hp,hr⟩; exact Eval.bind_success (Eval.guard_true hp) hr

theorem pure_success {α : Type} (x y : α) (n finish : Nat) :
    Eval SpecTec.Body (.pure x) n (.success (.of y)) finish ↔ y=x ∧ finish=n := by
  constructor
  · intro h; cases h; exact ⟨rfl,rfl⟩
  · rintro ⟨rfl,rfl⟩; exact Eval.pure _

#print axioms bind_known
end properties.wasm_module_ok.ConstructiveBodyEvalReduction
