import properties.wasm_module_ok.SubtypeListSupertypePosition

set_option autoImplicit false

namespace properties.wasm_module_ok.RollSubtypePosition

open properties.wasm_module_not_ok.Rejection

theorem rollSubtypes_get?_source
    (sts : List SpecTec.subtype) (x y i : Nat)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (h : sts[i]? = some (.SubT fin hts strt)) :
    (rollSubtypes sts x y)[i]? =
      some (.SubT fin (rollHeaptypes hts x y) (rollStrtype strt x y)) := by
  simp [rollSubtypes, rollSubtype, h]

end properties.wasm_module_ok.RollSubtypePosition
