import properties.wasm_module_ok.ConstructiveBodyReferenceBranchMembers
import properties.wasm_module_ok.ConstructiveBodyReferenceBranchOriginal
import properties.wasm_module_ok.ConstructiveBodyFunctionCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceBranchCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyReferenceBranches ConstructiveBodyReferenceBranchMembers ConstructiveBodyProductionCoverage

theorem onNull (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.BR_ON_NULL x)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.BR_ON_NULL x) effect ∧ finish=n := by
  obtain ⟨e,nu,heap,hx,hp⟩ := ConstructiveBodyReferenceBranchOriginal.onNull c stack x effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs)
    (ConstructiveBodyReferenceBranches.onNull c stack env hs e nu heap hp) _ effect n finish
    (onNull_mem c stack env hs e nu heap hp) _ h
  simpa only [hx] using onNull_produces c stack env hs e nu heap hp

theorem onNonNull (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (x : Nat) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.BR_ON_NON_NULL x)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.BR_ON_NON_NULL x) effect ∧ finish=n := by
  obtain ⟨label,nu,heap,hx,hp,hm⟩ := ConstructiveBodyReferenceBranchOriginal.onNonNull c stack env hs x effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs)
    (ConstructiveBodyReferenceBranches.onNonNull c stack env hs label nu heap hp hm) _ effect n finish
    (onNonNull_mem c stack env hs label nu heap hp hm) _ h
  simpa only [hx] using onNonNull_produces c stack env hs label nu heap hp hm

theorem onCast (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (x : Nat) (r1 r2 : reftype) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.BR_ON_CAST x r1 r2)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.BR_ON_CAST x r1 r2) effect ∧ finish=n := by
  obtain ⟨label,a,b,hx,ha,hb,hr,hm⟩ := ConstructiveBodyReferenceBranchOriginal.onCast c stack env x r1 r2 effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs)
    (ConstructiveBodyReferenceBranches.onCast c stack env label a b hr hm) _ effect n finish
    (onCast_mem c stack env hs label a b hr hm) _ h
  simpa only [hx,ha,hb] using onCast_produces c stack env label a b hr hm

theorem onCastFail (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (x : Nat) (r1 r2 : reftype) (effect : inferinstrtype) (n finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.BR_ON_CAST_FAIL x r1 r2)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.BR_ON_CAST_FAIL x r1 r2) effect ∧ finish=n := by
  obtain ⟨label,a,b,hx,ha,hb,hr,hm⟩ := ConstructiveBodyReferenceBranchOriginal.onCastFail c stack env x r1 r2 effect n finish h
  apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs)
    (ConstructiveBodyReferenceBranches.onCastFail c stack env label a b hr hm) _ effect n finish
    (onCastFail_mem c stack env hs label a b hr hm) _ h
  simpa only [hx,ha,hb] using onCastFail_produces c stack env label a b hr hm

#print axioms onCastFail
end properties.wasm_module_ok.ConstructiveBodyReferenceBranchCoverage
