import properties.wasm_module_ok.ValidatedMatchExistsBridge
import properties.wasm_module_ok.ValidatedMatchDeftypeTotal

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedTypeMatchExistsTotal

theorem validated_type_match_exists_total
    (c : SpecTec.context) (p q start : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length) :
    ∃ dtP dtQ : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ htsU : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
    ∃ r : Bool,
      c.TYPES[p]? = some dtP ∧
      c.TYPES[q]? = some dtQ ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dtP⟩)
        start (.success (.of (SpecTec.subtype.SubT fin htsU strtU))) start ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype_exists» c.TYPES htsU dtQ⟩)
        start (.success (.of r)) start := by
  let dtQ : SpecTec.deftype := c.TYPES[q]
  have hQ : c.TYPES[q]? = some dtQ := List.getElem?_eq_getElem hq
  obtain ⟨dtP, fin, htsU, strtU, r, hP, hunroll, hexists⟩ :=
    ValidatedMatchExistsBridge.validated_type_match_exists_of_predecessors
      c p dtQ start hc hp (by
        intro k dtK hkp hK
        exact ValidatedMatchDeftypeTotal.validated_match_deftype_total
          c k q start dtK dtQ hc (Nat.lt_trans hkp hp) hq hK hQ)
  exact ⟨dtP, dtQ, fin, htsU, strtU, r, hP, hQ, hunroll, hexists⟩

end properties.wasm_module_ok.ValidatedTypeMatchExistsTotal
