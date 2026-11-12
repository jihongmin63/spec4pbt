import properties.wasm_module_ok.RangeZipPosition
import properties.wasm_module_ok.RectypeRangeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeStaticBound

theorem rectype_ok_source_static_lt
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish i j k : Nat) (fin : SpecTec.final)
    (hts : List SpecTec.heaptype) (strt : SpecTec.strtype)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hstatic : hts[j]? = some (.VarHT (.StatX k))) :
    k < c.TYPES.length + i := by
  obtain ⟨dts, hc, hbound⟩ :=
    properties.wasm_module_ok.MatchHeaptypeBasic.rectype_ok_range_pairs_static_lt
      c c' sts start finish h
  have hpair :=
    properties.wasm_module_ok.RangeZipPosition.range_zip_source_position
      sts i (.SubT fin hts strt) hi hsource
  have hmem : SpecTec.heaptype.VarHT (.StatX k) ∈ hts :=
    List.mem_iff_getElem?.2 ⟨j, hstatic⟩
  exact hbound i fin hts strt hpair k hmem

end properties.wasm_module_ok.RectypeStaticBound
