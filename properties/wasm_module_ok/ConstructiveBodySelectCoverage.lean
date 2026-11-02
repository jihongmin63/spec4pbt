import properties.wasm_module_ok.ConstructiveBodySelectProductions
import properties.wasm_module_ok.ConstructiveBodySelectOriginal
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodySelectCoverage
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodySelectProductions ConstructiveBodyProductionCoverage

theorem plain_produces (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (hp : ConstructiveBodySelectCalls.plainAllowed stack=true) : Produces (plain c stack env hs hp) (.SELECT none) := by
  unfold Produces plain ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem typed_produces (c : context) (stack : inferresulttype) (env : Env c) (t : valtype)
    (ht : t∈FiniteValidTypes.validCandidates c) : Produces (typed c stack env t ht) (.SELECT (some [t])) := by
  unfold Produces typed ConstructiveBodyIndexedProductions.fixed ConstructiveBodySimpleAtoms.unchanged
  simp only [ConstructiveConstTableCore.Audited.pure,Gen.support]
  exact ⟨_,rfl,rfl⟩

theorem original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (ts : Option (List valtype)) (effect : inferinstrtype) (n finish : Nat) (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨inferinstrtype,Call.Instr_ok c stack (.SELECT ts)⟩) n (.success (.of effect)) finish) :
    Covers (all c stack env hs) (.SELECT ts) effect ∧ finish=n := by
  cases ts with
  | none =>
    have hp : ConstructiveBodySelectCalls.plainAllowed stack=true := Bool.or_eq_true_iff.mpr (ConstructiveBodySelectOriginal.plain c stack effect n finish h)
    apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs) (plain c stack env hs hp) _ effect n finish
      _ (plain_produces c stack env hs hp) h
    apply List.mem_append_right
    simp only [hp,dite_true]
    exact List.mem_singleton_self _
  | some ts =>
    obtain ⟨t,rfl,hv⟩ := ConstructiveBodySelectOriginal.typed c stack ts effect n finish h
    have ht := (FiniteValidTypes.validCandidates_spec c t).2 hv
    apply ConstructiveBodyFunctionCoverage.from_production c stack (all c stack env hs) (typed c stack env t ht) _ effect n finish
      _ (typed_produces c stack env t ht) h
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨⟨t,ht⟩,by simp,rfl⟩

#print axioms original
end properties.wasm_module_ok.ConstructiveBodySelectCoverage
