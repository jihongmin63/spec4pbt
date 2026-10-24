import properties.wasm_module_not_ok.bundle.Contract

namespace properties.wasm_module_not_ok.Proof

theorem property_correct : properties.wasm_module_not_ok.bundle.Contract.property := by
  intro input premise
  rfl

end properties.wasm_module_not_ok.Proof
