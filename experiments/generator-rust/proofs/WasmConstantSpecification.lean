import WasmDomainWitnesses

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000

namespace RustWasm
open SpecTecExecution

/- Reduce guards in the kernel even when their syntax still mentions the literal. -/
syntax "constant_spec_run" : tactic
macro_rules
| `(tactic| constant_spec_run) => `(tactic|
  first
  | exact Eval.pure _
  | exact Eval.unmatch
  | (apply Eval.guard_true; exact of_decide_eq_true rfl)
  | (apply Eval.guard_false; exact of_decide_eq_true rfl)
  | (apply Eval.call; constant_spec_run)
  | (apply Eval.bind_success; constant_spec_run; constant_spec_run)
  | (apply Eval.bind_unmatch; constant_spec_run)
  | (apply Eval.orElse_success; constant_spec_run)
  | (apply Eval.orElse_unmatch; constant_spec_run; constant_spec_run))

/-- The requested exact one-instruction body in the original specification AST. -/
def constantModule (n : Nat) : SpecTec.module :=
  { emptyModule with
    TYPES := [.RecT [.SubT .Final [] (.DefFuncT (.FuncT [] [.NumT .I32T]))]]
    FUNCS := [⟨0, [], [.CONST (.I32 n)]⟩] }

/-- Original validation imposes no machine-word bound on this literal. -/
theorem constant_module_ok (n : Nat) : SpecTec.Module_ok (constantModule n) := by
  refine ⟨0, ?_⟩
  constant_spec_run

/-- Original i64 literals also range over all naturals, independently of binary encoding. -/
def constant64Module (n : Nat) : SpecTec.module :=
  { emptyModule with
    TYPES := [.RecT [.SubT .Final [] (.DefFuncT (.FuncT [] [.NumT .I64T]))]]
    FUNCS := [⟨0, [], [.CONST (.I64 n)]⟩] }

theorem constant64_module_ok (n : Nat) : SpecTec.Module_ok (constant64Module n) := by
  refine ⟨0, ?_⟩
  constant_spec_run

end RustWasm
