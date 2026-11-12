import properties.wasm_module_ok.SubstOutputValtypes

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstOutputFields

open properties.wasm_module_not_ok.Rejection

theorem substStoragetypeResult_output_fixed
    (st : SpecTec.storagetype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.storagetype)
    (h : substStoragetypeResult st pref = some result) :
    substStoragetypeResult result dts = some result := by
  cases st with
  | ValStorageT t =>
      cases ht : substValtypeResult t pref with
      | none => simp [substStoragetypeResult, ht] at h
      | some t' =>
          have hr : result = SpecTec.storagetype.ValStorageT t' := by
            simpa [substStoragetypeResult, ht] using h.symm
          subst result
          simp [substStoragetypeResult,
            SubstOutputValtypes.substValtypeResult_output_fixed
              t pref dts t' ht]
  | PackStorageT pt =>
      have hr : result = SpecTec.storagetype.PackStorageT pt := by
        simpa [substStoragetypeResult] using h.symm
      subst result
      rfl

theorem substFieldtypeResult_output_fixed
    (ft : SpecTec.fieldtype) (pref dts : List SpecTec.deftype)
    (result : SpecTec.fieldtype)
    (h : substFieldtypeResult ft pref = some result) :
    substFieldtypeResult result dts = some result := by
  cases ft with
  | FieldT mu st =>
      cases hs : substStoragetypeResult st pref with
      | none => simp [substFieldtypeResult, hs] at h
      | some st' =>
          have hr : result = SpecTec.fieldtype.FieldT mu st' := by
            simpa [substFieldtypeResult, hs] using h.symm
          subst result
          simp [substFieldtypeResult,
            substStoragetypeResult_output_fixed st pref dts st' hs]

theorem substFieldtypeListResult_output_fixed
    (fts : List SpecTec.fieldtype) (pref dts : List SpecTec.deftype)
    (result : List SpecTec.fieldtype)
    (h : substFieldtypeListResult fts pref = some result) :
    substFieldtypeListResult result dts = some result := by
  induction fts generalizing result with
  | nil =>
      have hr : result = [] := by
        simpa [substFieldtypeListResult] using h.symm
      subst result
      rfl
  | cons ft fts ih =>
      cases hhead : substFieldtypeResult ft pref with
      | none => simp [substFieldtypeListResult, hhead] at h
      | some ft' =>
          cases hrest : substFieldtypeListResult fts pref with
          | none => simp [substFieldtypeListResult, hhead, hrest] at h
          | some fts' =>
              have hr : result = ft' :: fts' := by
                simpa [substFieldtypeListResult, hhead, hrest] using h.symm
              subst result
              simp [substFieldtypeListResult,
                substFieldtypeResult_output_fixed ft pref dts ft' hhead,
                ih fts' hrest]

end properties.wasm_module_ok.SubstOutputFields
