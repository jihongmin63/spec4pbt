import properties.wasm_module_ok.SubtypeResultShape

set_option autoImplicit false

namespace properties.wasm_module_ok.SubtypeListSupertypePosition

open properties.wasm_module_not_ok.Rejection

theorem substSubtypeListResult_supertype_position
    (sts sts' : List SpecTec.subtype)
    (dts : List SpecTec.deftype)
    (i j : Nat) (fin : SpecTec.final)
    (hts : List SpecTec.heaptype) (strt : SpecTec.strtype)
    (h : substSubtypeListResult sts dts = some sts')
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hj : j < hts.length) :
    ∃ hts' : List SpecTec.heaptype,
      ∃ strt' : SpecTec.strtype,
      ∃ ht ht' : SpecTec.heaptype,
        sts'[i]? = some (.SubT fin hts' strt') ∧
        hts[j]? = some ht ∧ hts'[j]? = some ht' ∧
        substHeaptypeResult ht dts = some ht' := by
  obtain ⟨st, st', hget, hget', hsubst⟩ :=
    properties.wasm_module_ok.SubstSubtypeListPosition.substSubtypeListResult_position
      sts dts sts' i h hi
  rw [hsource] at hget
  cases hget
  obtain ⟨hts', strt', ht, ht', hshape, hht, hht', hresult⟩ :=
    properties.wasm_module_ok.SubtypeResultShape.substSubtypeResult_supertype_position
      fin hts strt dts st' j hsubst hj
  subst st'
  exact ⟨hts', strt', ht, ht', hget', hht, hht', hresult⟩

end properties.wasm_module_ok.SubtypeListSupertypePosition
