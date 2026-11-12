import properties.wasm_module_not_ok.TypeFamilyCodec
import properties.wasm_module_not_ok.GeneratorCore

set_option autoImplicit false

namespace properties.wasm_module_not_ok.ModuleGenerator

open properties.wasm_module_not_ok.GeneratorCore

def allModules : Gen SpecTec.module :=
  encodableFilter (fun _ => true)

theorem support_allModules :
    Gen.support allModules = fun _ : SpecTec.module => True := by
  rw [allModules, support_encodableFilter]
  funext m
  apply propext
  simp

end properties.wasm_module_not_ok.ModuleGenerator
