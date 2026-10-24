import properties.wasm_module_ok.bundle.Contract
import properties.wasm_module_not_ok.ModuleGenerator

set_option autoImplicit false

namespace properties.wasm_module_ok.InputEnumeration

private abbrev Input := properties.wasm_module_ok.bundle.Contract.Input

/-- Every full Wasm module, wrapped in the exact generated input type. -/
def allInputs : Gen Input :=
  (fun m : SpecTec.module => { m := m }) <$>
    properties.wasm_module_not_ok.ModuleGenerator.allModules

theorem support_allInputs :
    Gen.support allInputs = fun _ : Input => True := by
  funext input
  apply propext
  simp only [allInputs, Gen.Support.support_map]
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨input.m, ?_, ?_⟩
    · simp [properties.wasm_module_not_ok.ModuleGenerator.support_allModules]
    · cases input
      rfl

theorem module_roundtrip (m : SpecTec.module) :
    Encodable.decode (Encodable.encode m) = some m :=
  Encodable.encodek m

theorem everyInputEncoded (input : Input) :
    ∃ n : Nat, (Encodable.decode n : Option SpecTec.module) = some input.m :=
  ⟨Encodable.encode input.m, module_roundtrip input.m⟩

end properties.wasm_module_ok.InputEnumeration
