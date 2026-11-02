import properties.wasm_module_ok.ConstructiveModulePreludeTypes
import properties.wasm_module_ok.ConstructiveModuleStart
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleGeneration
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore

structure Result where
  prelude : ConstructiveModulePrelude.Result
  functions : ConstructiveModuleFunctionList.Result (ConstructiveModulePrelude.finalContext prelude)
    (prelude.before.headers.items.map (·.FTYPE))
  start : ConstructiveModuleStart.Result (ConstructiveModulePrelude.finalContext prelude)

def module (out : Result) : SpecTec.module :=
  {ConstructiveModulePrelude.raw out.prelude with FUNCS:=out.functions.items,START:=out.start.val}

def generate : Gen Result := do
  let p ← ConstructiveModulePrelude.generate
  let fs ← (ConstructiveModuleFunctionList.generate (ConstructiveModulePrelude.finalContext p) (ConstructiveModulePrelude.finalEnv p)
    (p.before.headers.items.map (·.FTYPE)) (ConstructiveModulePrelude.headers_ready p)).generator
  let s ← ConstructiveModuleStart.generate (ConstructiveModulePrelude.finalContext p)
  pure ⟨p,fs,s⟩

def modules : Gen SpecTec.module := module <$> generate

theorem generate_audit : ConstructiveGenAudit.Structural generate :=
  ⟨ConstructiveModulePrelude.generate_audit,fun p => ⟨(ConstructiveModuleFunctionList.generate _ _ _ (ConstructiveModulePrelude.headers_ready p)).audit,
    fun _ => ⟨ConstructiveModuleStart.generate_audit _,fun _ => trivial⟩⟩⟩
theorem modules_audit : ConstructiveGenAudit.Structural modules :=
  (ConstructiveGenAudit.map_audit _ _).2 generate_audit
#print axioms modules_audit
end properties.wasm_module_ok.ConstructiveModuleGeneration
