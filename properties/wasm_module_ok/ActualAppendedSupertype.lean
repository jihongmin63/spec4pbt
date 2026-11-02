import properties.wasm_module_ok.RectypeStaticBound
import properties.wasm_module_ok.RectypeAppendedShape

set_option autoImplicit false

namespace properties.wasm_module_ok.ActualAppendedSupertype

theorem rectype_ok_appended_static_supertype
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish i j k : Nat) (fin : SpecTec.final)
    (hts : List SpecTec.heaptype) (strt : SpecTec.strtype)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hj : j < hts.length)
    (hstatic : hts[j]? = some (.VarHT (.StatX k))) :
    ∃ dts : List SpecTec.deftype,
      ∃ sts' : List SpecTec.subtype,
      ∃ hts' : List SpecTec.heaptype,
      ∃ strt' : SpecTec.strtype,
        c' = {c with TYPES := c.TYPES ++ dts} ∧
        dts[i]? = some (.DefT (.RecT sts') i) ∧
        sts'[i]? = some (.SubT fin hts' strt') ∧
        hts'[j]? =
          if k < c.TYPES.length then
            (c.TYPES[k]?).map SpecTec.heaptype.DefHT
          else some (.VarHT (.RecX (k - c.TYPES.length))) := by
  have hk :=
    properties.wasm_module_ok.RectypeStaticBound.rectype_ok_source_static_lt
      c c' sts start finish i j k fin hts strt h hi hsource hstatic
  obtain ⟨dts, hc, hpos⟩ :=
    properties.wasm_module_ok.RectypeAppendedShape.rectype_ok_appended_position_shape
      c c' sts start finish h
  obtain ⟨rect', hget, hresult⟩ := hpos i hi
  obtain ⟨sts', hts', strt', hrect, hst', hht'⟩ :=
    properties.wasm_module_ok.DescendingSupertypeResult.descending_static_supertype_result
      sts c.TYPES rect' c.TYPES.length i j k fin hts strt
      hresult hi hsource hj hstatic hk
  subst rect'
  exact ⟨dts, sts', hts', strt', hc, hget, hst', hht'⟩

end properties.wasm_module_ok.ActualAppendedSupertype
