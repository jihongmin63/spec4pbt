import properties.wasm_module_ok.ValidatedTypeUnroll

set_option autoImplicit false

namespace properties.wasm_module_ok.UnrollPositionBridge

open properties.wasm_module_not_ok.Rejection

theorem unroll_deftype_at
    (sts' : List SpecTec.subtype) (i : Nat)
    (fin : SpecTec.final) (hts' : List SpecTec.heaptype)
    (strt' : SpecTec.strtype)
    (hget : sts'[i]? = some (.SubT fin hts' strt')) :
    unrollDeftypeResult (.DefT (.RecT sts') i) =
      some (.SubT fin (unrollHeaptypes hts' (.RecT sts'))
        (unrollStrtype strt' (.RecT sts'))) := by
  simp [unrollDeftypeResult, unrollRectype, unrollSubtypes,
    unrollSubtype, hget]

theorem unroll_heaptypes_at
    (hts : List SpecTec.heaptype) (rect : SpecTec.rectype)
    (j : Nat) (ht : SpecTec.heaptype)
    (hget : hts[j]? = some ht) :
    (unrollHeaptypes hts rect)[j]? = some (unrollHeaptype ht rect) := by
  simp [unrollHeaptypes, hget]

end properties.wasm_module_ok.UnrollPositionBridge
