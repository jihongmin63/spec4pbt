import properties.wasm_module_ok.RollTypevarDescending

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstHeaptypeListPosition

open properties.wasm_module_not_ok.Rejection

theorem substHeaptypeListResult_position
    (hts : List SpecTec.heaptype) (dts : List SpecTec.deftype)
    (hts' : List SpecTec.heaptype) (i : Nat)
    (h : substHeaptypeListResult hts dts = some hts')
    (hi : i < hts.length) :
    ∃ ht ht' : SpecTec.heaptype,
      hts[i]? = some ht ∧ hts'[i]? = some ht' ∧
      substHeaptypeResult ht dts = some ht' := by
  induction hts generalizing hts' i with
  | nil => simp at hi
  | cons hd tl ih =>
      cases hhd : substHeaptypeResult hd dts with
      | none =>
          simp [substHeaptypeListResult, hhd] at h
      | some hd' =>
          cases htl : substHeaptypeListResult tl dts with
          | none =>
              simp [substHeaptypeListResult, hhd, htl] at h
          | some tl' =>
              simp [substHeaptypeListResult, hhd, htl] at h
              cases h
              cases i with
              | zero => exact ⟨hd, hd', rfl, rfl, hhd⟩
              | succ j =>
                  have hj : j < tl.length := by simpa using hi
                  obtain ⟨ht, ht', hget, hget', hsubst⟩ :=
                    ih tl' j htl hj
                  exact ⟨ht, ht', hget, hget', hsubst⟩

end properties.wasm_module_ok.SubstHeaptypeListPosition
