import properties.wasm_module_ok.bundle.Contract
import properties.wasm_module_ok.ConstructiveModuleCompleteness

set_option autoImplicit false
namespace properties.wasm_module_ok.Generator
open properties.wasm_module_ok.bundle

/-- Construct the exact original module syntax from productive typed choices.
The generator contains no candidate validation or rejection path. -/
def generator : Contract.generatorValue :=
  (fun m => (⟨m⟩ : Contract.Input)) <$> ConstructiveModuleGeneration.modules

theorem soundness : Contract.generatorSound generator := by
  intro input h
  obtain ⟨m,hm,he⟩ := h
  subst input
  exact ConstructiveModuleGeneration.modules_sound m hm

theorem completeness : Contract.generatorComplete generator := by
  intro input h
  exact ⟨input.m,ConstructiveModuleGeneration.modules_complete input.m h,by cases input;rfl⟩

/-- Every reachable generator node and continuation is free of assume, and
 every indexed family is monotone over its complete support. Host metadata
 choices are reviewed separately in ConstructiveGenerator.md. -/
theorem structural : ConstructiveGenAudit.Structural generator :=
  (ConstructiveGenAudit.map_audit _ _).2 ConstructiveModuleGeneration.modules_audit

theorem total : Gen.total generator := ConstructiveGenAudit.audit_total _ structural

end properties.wasm_module_ok.Generator
