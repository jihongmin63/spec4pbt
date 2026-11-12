import properties.wasm_module_ok.SubstHeaptypeListPosition

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstSubtypeListPosition

open properties.wasm_module_not_ok.Rejection

theorem substSubtypeListResult_position
    (sts : List SpecTec.subtype) (dts : List SpecTec.deftype)
    (sts' : List SpecTec.subtype) (i : Nat)
    (h : substSubtypeListResult sts dts = some sts')
    (hi : i < sts.length) :
    ∃ st st' : SpecTec.subtype,
      sts[i]? = some st ∧ sts'[i]? = some st' ∧
      substSubtypeResult st dts = some st' := by
  induction sts generalizing sts' i with
  | nil => simp at hi
  | cons hd tl ih =>
      cases hhd : substSubtypeResult hd dts with
      | none =>
          simp [substSubtypeListResult, hhd] at h
      | some hd' =>
          cases htl : substSubtypeListResult tl dts with
          | none =>
              simp [substSubtypeListResult, hhd, htl] at h
          | some tl' =>
              simp [substSubtypeListResult, hhd, htl] at h
              cases h
              cases i with
              | zero => exact ⟨hd, hd', rfl, rfl, hhd⟩
              | succ j =>
                  have hj : j < tl.length := by simpa using hi
                  obtain ⟨st, st', hget, hget', hsubst⟩ :=
                    ih tl' j htl hj
                  exact ⟨st, st', hget, hget', hsubst⟩

end properties.wasm_module_ok.SubstSubtypeListPosition
