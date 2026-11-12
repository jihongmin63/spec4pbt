import properties.wasm_module_ok.SubstPrefixValtypes

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstPrefixFields

open properties.wasm_module_not_ok.Rejection

theorem substStoragetypeResult_prefix
    (st : SpecTec.storagetype)
    (pref tail : List SpecTec.deftype)
    (result : SpecTec.storagetype)
    (h : substStoragetypeResult st pref = some result) :
    substStoragetypeResult st (pref ++ tail) = some result := by
  cases st with
  | ValStorageT t =>
      cases ht : substValtypeResult t pref with
      | none => simp [substStoragetypeResult, ht] at h
      | some t' =>
          have hr : result = SpecTec.storagetype.ValStorageT t' := by
            simpa [substStoragetypeResult, ht] using h.symm
          subst result
          simp [substStoragetypeResult,
            SubstPrefixValtypes.substValtypeResult_prefix t pref tail t' ht]
  | PackStorageT pt => simpa [substStoragetypeResult] using h

theorem substFieldtypeResult_prefix
    (ft : SpecTec.fieldtype)
    (pref tail : List SpecTec.deftype)
    (result : SpecTec.fieldtype)
    (h : substFieldtypeResult ft pref = some result) :
    substFieldtypeResult ft (pref ++ tail) = some result := by
  cases ft with
  | FieldT mu st =>
      cases hst : substStoragetypeResult st pref with
      | none => simp [substFieldtypeResult, hst] at h
      | some st' =>
          have hr : result = SpecTec.fieldtype.FieldT mu st' := by
            simpa [substFieldtypeResult, hst] using h.symm
          subst result
          simp [substFieldtypeResult,
            substStoragetypeResult_prefix st pref tail st' hst]

theorem substFieldtypeListResult_prefix
    (fts : List SpecTec.fieldtype)
    (pref tail : List SpecTec.deftype)
    (result : List SpecTec.fieldtype)
    (h : substFieldtypeListResult fts pref = some result) :
    substFieldtypeListResult fts (pref ++ tail) = some result := by
  induction fts generalizing result with
  | nil => simpa [substFieldtypeListResult] using h
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
                substFieldtypeResult_prefix ft pref tail ft' hhead,
                ih fts' hrest]

end properties.wasm_module_ok.SubstPrefixFields
