import properties.wasm_module_ok.ValidatedMatchIndexResult
import properties.wasm_module_ok.ValidatedMatchHeaptypeResult

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchHeaptypeIndex

theorem validated_match_heaptype_def_pair_index_iff
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype) (result : Bool)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» c.TYPES
        (.DefHT dtP) (.DefHT dtQ)⟩)
      start (.success (.of result)) start ↔
    result = ValidatedMatchIndexFuel.matchIndex c p q := by
  exact (ValidatedMatchHeaptypeResult.validated_match_heaptype_def_pair_result_iff
    c p q start dtP dtQ result hc hp hq hP hQ).trans
    (ValidatedMatchIndexResult.validated_match_index_result_iff
      c p q start dtP dtQ result hc hp hq hP hQ)

end properties.wasm_module_ok.ValidatedMatchHeaptypeIndex
