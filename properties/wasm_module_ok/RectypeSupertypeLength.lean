import properties.wasm_module_ok.SupertypeLength
import properties.wasm_module_ok.SubstRectypePosition
import properties.wasm_module_ok.SubstSubtypeListPosition

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeSupertypeLength

open properties.wasm_module_not_ok.Rejection

theorem rectype_subst_supertype_length
    (sts sts' : List SpecTec.subtype)
    (dts : List SpecTec.deftype) (x y i : Nat)
    (fin : SpecTec.final) (hts hts' : List SpecTec.heaptype)
    (strt strt' : SpecTec.strtype)
    (hresult : substRectypeResult
      (.RecT (rollSubtypes sts x y)) dts = some (.RecT sts'))
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (htrans : sts'[i]? = some (.SubT fin hts' strt')) :
    hts'.length = hts.length := by
  have hi : i < sts.length :=
    (List.getElem?_eq_some_iff.mp hsource).choose
  obtain ⟨result, hrect, hsub⟩ :=
    SubstRectypePosition.substRectypeResult_subtypes
      (rollSubtypes sts x y) dts (.RecT sts') hresult
  have hresultEq : result = sts' := by
    injection hrect with heq
    exact heq.symm
  subst result
  have hrolled :=
    RollSubtypePosition.rollSubtypes_get?_source
      sts x y i fin hts strt hsource
  have hirolled : i < (rollSubtypes sts x y).length := by
    simpa [rollSubtypes] using hi
  obtain ⟨src, dst, hsrc, hdst, hsubst⟩ :=
    SubstSubtypeListPosition.substSubtypeListResult_position
      (rollSubtypes sts x y) dts sts' i hsub hirolled
  have hsrcEq :
      src = .SubT fin (rollHeaptypes hts x y) (rollStrtype strt x y) :=
    Option.some.inj (hsrc.symm.trans hrolled)
  have hdstEq : dst = .SubT fin hts' strt' :=
    Option.some.inj (hdst.symm.trans htrans)
  subst src
  subst dst
  have hlen := SupertypeLength.substSubtypeResult_supers_length
    fin fin (rollHeaptypes hts x y) hts'
    (rollStrtype strt x y) strt' dts hsubst
  simpa [rollHeaptypes] using hlen

end properties.wasm_module_ok.RectypeSupertypeLength
