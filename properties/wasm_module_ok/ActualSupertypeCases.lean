import properties.wasm_module_ok.ActualAppendedSupertype

set_option autoImplicit false

namespace properties.wasm_module_ok.ActualSupertypeCases

theorem rectype_ok_appended_static_supertype_cases
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish i j k : Nat) (fin : SpecTec.final)
    (hts : List SpecTec.heaptype) (strt : SpecTec.strtype)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
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
        ((∃ dt : SpecTec.deftype,
            k < c.TYPES.length ∧ c.TYPES[k]? = some dt ∧
            hts'[j]? = some (.DefHT dt)) ∨
          (c.TYPES.length ≤ k ∧ k - c.TYPES.length < i ∧
            hts'[j]? = some (.VarHT (.RecX (k - c.TYPES.length))))) := by
  obtain ⟨dts, sts', hts', strt', hc, hdts, hsts, hhts⟩ :=
    properties.wasm_module_ok.ActualAppendedSupertype.rectype_ok_appended_static_supertype
      c c' sts start finish i j k fin hts strt h hi hsource hj hstatic
  refine ⟨dts, sts', hts', strt', hc, hdts, hsts, ?_⟩
  by_cases hlt : k < c.TYPES.length
  · have hlookup : c.TYPES[k]? = some c.TYPES[k] :=
      List.getElem?_eq_getElem hlt
    left
    refine ⟨c.TYPES[k], hlt, hlookup, ?_⟩
    simpa [hlt, hlookup] using hhts
  · have hge : c.TYPES.length ≤ k := Nat.le_of_not_gt hlt
    have hk :=
      properties.wasm_module_ok.RectypeStaticBound.rectype_ok_source_static_lt
        c c' sts start finish i j k fin hts strt h hi hsource hstatic
    have hdiff : k - c.TYPES.length < i := by omega
    right
    refine ⟨hge, hdiff, ?_⟩
    simpa [hlt] using hhts

end properties.wasm_module_ok.ActualSupertypeCases
