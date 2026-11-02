/- Property-local positive runtime refinement for the unchanged Wasm specification.
   Original source identity: s41537f07a12c318563e6aabf63ee533b7bcdb33a44bfeb071c4af4b8ddd8bf9a.
   Executable definitions and erasure proofs are separate; no compiler replacements. -/
import properties.wasm_module_ok.PositiveCalls
namespace properties.wasm_module_ok.PositiveRuntime
open SpecTecExecution
set_option autoImplicit false
set_option maxRecDepth 10000

noncomputable def erase {α : Type} : ExecutablePlan Call α → Plan SpecTec.SpecTecRequest
  | .pure v => .pure v
  | .unmatch => .unmatch
  | .abort m => .abort m
  | .freshId => .freshId
  | .call c => .call ⟨_, toOriginal c⟩
  | .primitive c => .primitive ⟨_, toOriginal c⟩
  | @ExecutablePlan.guard _ p _ => .guard p
  | .bind p k => .bind (erase p) (fun x => erase (k x))
  | .orElse p k => .orElse (erase p) (fun x => erase (k x))
  | .notHold p => .notHold (erase p)

 theorem erase_firstSuccess {I α : Type}
    (cs : List (ExecutablePlan.Clause Call I α)) (i : I) :
    erase (ExecutablePlan.firstSuccess cs i) =
      firstSuccess (cs.map (fun c i => erase (c i))) i := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [ExecutablePlan.firstSuccess, erase, List.map_cons, firstSuccess, ih]
end properties.wasm_module_ok.PositiveRuntime
