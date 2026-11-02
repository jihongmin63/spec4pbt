import properties.wasm_module_ok.RollHeaptypePosition
import properties.wasm_module_ok.RollTypevarDescending

set_option autoImplicit false

namespace properties.wasm_module_ok.DescendingSupertypeResult

open properties.wasm_module_not_ok.Rejection

theorem descending_static_supertype_result
    (sts : List SpecTec.subtype) (dts : List SpecTec.deftype)
    (rect' : SpecTec.rectype) (x i j k : Nat)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (hresult : substRectypeResult
      (.RecT (rollSubtypes sts x (sts.length + x))) dts = some rect')
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hj : j < hts.length)
    (hstatic : hts[j]? = some (.VarHT (.StatX k)))
    (hk : k < x + i) :
    ∃ sts' : List SpecTec.subtype,
      ∃ hts' : List SpecTec.heaptype,
      ∃ strt' : SpecTec.strtype,
        rect' = .RecT sts' ∧
        sts'[i]? = some (.SubT fin hts' strt') ∧
        hts'[j]? =
          if k < x then (dts[k]?).map SpecTec.heaptype.DefHT
          else some (.VarHT (.RecX (k - x))) := by
  obtain ⟨sts', hts', strt', ht, ht', hrect, hget, hrolled, hget', hsubst⟩ :=
    properties.wasm_module_ok.RectypeSupertypePosition.rectype_subst_supertype_position
      sts dts rect' x (sts.length + x) i j fin hts strt
      hresult hi hsource hj
  have hrollstatic :=
    properties.wasm_module_ok.RollHeaptypePosition.rollHeaptypes_get?_static
      hts x (sts.length + x) j k hstatic
  rw [hrollstatic] at hrolled
  cases hrolled
  have hdesc :=
    properties.wasm_module_ok.RollTypevarDescending.substHeaptypeResult_descending
      dts x sts.length i k hi hk
  rw [hdesc] at hsubst
  refine ⟨sts', hts', strt', hrect, hget, ?_⟩
  calc
    hts'[j]? = some ht' := hget'
    _ = if k < x then (dts[k]?).map SpecTec.heaptype.DefHT
        else some (.VarHT (.RecX (k - x))) := hsubst.symm

end properties.wasm_module_ok.DescendingSupertypeResult
