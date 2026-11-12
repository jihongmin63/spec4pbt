import properties.wasm_module_ok.SubstPrefixTypevar

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstPrefixHeaptype

open properties.wasm_module_not_ok.Rejection

theorem substHeaptypeResult_prefix
    (ht : SpecTec.heaptype)
    (pref tail : List SpecTec.deftype)
    (result : SpecTec.heaptype)
    (h : substHeaptypeResult ht pref = some result) :
    substHeaptypeResult ht (pref ++ tail) = some result := by
  cases ht <;> simp_all [substHeaptypeResult,
    SubstPrefixTypevar.substOfResult_prefix]

end properties.wasm_module_ok.SubstPrefixHeaptype
