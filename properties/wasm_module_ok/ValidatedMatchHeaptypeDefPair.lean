import properties.wasm_module_ok.ValidatedMatchDeftypeTotal

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchHeaptypeDefPair

theorem validated_match_heaptype_def_pair_total
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype» c.TYPES
            (.DefHT dtP) (.DefHT dtQ)⟩)
        start (.success (.of r)) start := by
  obtain ⟨r, hmatch⟩ :=
    ValidatedMatchDeftypeTotal.validated_match_deftype_total
      c p q start dtP dtQ hc hp hq hP hQ
  exact ⟨r,
    MatchHeaptypeBasic.match_heaptype_def_def_total_of_match_deftype
      c.TYPES dtP dtQ r start hmatch⟩

end properties.wasm_module_ok.ValidatedMatchHeaptypeDefPair
