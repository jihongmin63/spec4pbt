import properties.wasm_module_ok.RectypeSupertypePosition

set_option autoImplicit false

namespace properties.wasm_module_ok.RollHeaptypePosition

open properties.wasm_module_not_ok.Rejection

theorem rollHeaptypes_get?_static
    (hts : List SpecTec.heaptype) (x y j k : Nat)
    (h : hts[j]? = some (.VarHT (.StatX k))) :
    (rollHeaptypes hts x y)[j]? =
      some (rollTypevar (.StatX k) x y) := by
  simp [rollHeaptypes, rollHeaptype, h]

end properties.wasm_module_ok.RollHeaptypePosition
