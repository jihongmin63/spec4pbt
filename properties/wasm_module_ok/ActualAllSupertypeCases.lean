import properties.wasm_module_ok.RectypeAllStatic
import properties.wasm_module_ok.ActualSupertypeCases

set_option autoImplicit false

namespace properties.wasm_module_ok.ActualAllSupertypeCases

theorem rectype_ok_appended_all_supertype_cases
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish i j : Nat) (fin : SpecTec.final)
    (hts : List SpecTec.heaptype) (strt : SpecTec.strtype)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hj : j < hts.length) :
    ∃ k : Nat,
      hts[j]? = some (.VarHT (.StatX k)) ∧
      k < c.TYPES.length + i ∧
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
  have hmem : hts[j] ∈ hts :=
    List.mem_iff_getElem?.2 ⟨j, List.getElem?_eq_getElem hj⟩
  obtain ⟨k, hshape, hlt⟩ :=
    properties.wasm_module_ok.RectypeAllStatic.rectype_ok_source_all_static
      c c' sts start finish i fin hts strt h hi hsource
      hts[j] hmem
  have hstatic : hts[j]? = some (.VarHT (.StatX k)) := by
    simpa only [List.getElem?_eq_getElem hj, hshape]
  obtain ⟨dts, sts', hts', strt', hc, hdts, hsts, hcase⟩ :=
    properties.wasm_module_ok.ActualSupertypeCases.rectype_ok_appended_static_supertype_cases
      c c' sts start finish i j k fin hts strt h hi hsource hj hstatic
  exact ⟨k, hstatic, hlt, dts, sts', hts', strt', hc, hdts, hsts, hcase⟩

end properties.wasm_module_ok.ActualAllSupertypeCases
