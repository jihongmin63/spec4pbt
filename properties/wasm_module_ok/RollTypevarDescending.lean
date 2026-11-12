import properties.wasm_module_ok.SubstRectypeLength

set_option autoImplicit false

namespace properties.wasm_module_ok.RollTypevarDescending

open properties.wasm_module_not_ok.Rejection

theorem rollTypevar_descending
    (x len n y : Nat) (hn : n < len) (hy : y < x + n) :
    rollTypevar (.StatX y) x (len + x) =
      if y < x then .VarHT (.StatX y)
      else .VarHT (.RecX (y - x)) := by
  by_cases hlt : y < x
  · have hout : ¬ (x ≤ y ∧ y < len + x) := by omega
    simp [rollTypevar, hlt, hout]
  · have hin : x ≤ y ∧ y < len + x := by omega
    simp [rollTypevar, hlt, hin]

theorem substHeaptypeResult_descending
    (dts : List SpecTec.deftype) (x len n y : Nat)
    (hn : n < len) (hy : y < x + n) :
    substHeaptypeResult (rollTypevar (.StatX y) x (len + x)) dts =
      if y < x then (dts[y]?).map SpecTec.heaptype.DefHT
      else some (.VarHT (.RecX (y - x))) := by
  rw [rollTypevar_descending x len n y hn hy]
  by_cases hlt : y < x <;>
    simp [hlt, substHeaptypeResult, substOfResult]

end properties.wasm_module_ok.RollTypevarDescending
