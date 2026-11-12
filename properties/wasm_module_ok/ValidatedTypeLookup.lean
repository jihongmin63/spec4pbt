import properties.wasm_module_ok.ValidatedTypeEdges
import properties.wasm_module_ok.SubstRectypeLength

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedTypeLookup

open properties.wasm_module_ok.ValidatedTypeChain

theorem validated_types_position_lookup
    (c : SpecTec.context) (p : Nat)
    (hc : ValidatedTypes c) (hp : p < c.TYPES.length) :
    ∃ before after : SpecTec.context,
    ∃ sts : List SpecTec.subtype,
    ∃ start finish i : Nat,
    ∃ tail : List SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strt : SpecTec.strtype,
    ∃ dts : List SpecTec.deftype,
    ∃ sts' : List SpecTec.subtype,
      ValidatedTypes before ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context,
          SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
        start (.success (.of after)) finish ∧
      p = before.TYPES.length + i ∧ i < sts.length ∧
      sts[i]? = some (.SubT fin hts strt) ∧
      after = {before with TYPES := before.TYPES ++ dts} ∧
      dts[i]? = some (.DefT (.RecT sts') i) ∧
      after.TYPES[p]? = some (.DefT (.RecT sts') i) ∧
      c.TYPES = after.TYPES ++ tail ∧
      c.TYPES[p]? = some (.DefT (.RecT sts') i) := by
  obtain ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, hbefore, hrect, hpos, hi, hsource, hprefix⟩ :=
    validated_types_position_source c p hc hp
  obtain ⟨dts, hafter, hpositions⟩ :=
    SubstRectypeLength.rectype_ok_appended_inner_length
      before after sts start finish hrect
  obtain ⟨sts', hdts, _⟩ := hpositions i hi
  have hiDts : i < dts.length :=
    (List.getElem?_eq_some_iff.mp hdts).choose
  have hpAfter : p < after.TYPES.length := by
    rw [hpos, hafter, List.length_append]
    omega
  have hafterLookup :
      after.TYPES[p]? = some (.DefT (.RecT sts') i) := by
    rw [hpos, hafter]
    rw [List.getElem?_append_right (by omega)]
    have hidx : before.TYPES.length + i - before.TYPES.length = i := by
      omega
    rw [hidx]
    exact hdts
  have hcLookup :
      c.TYPES[p]? = some (.DefT (.RecT sts') i) := by
    rw [hprefix, List.getElem?_append_left hpAfter]
    exact hafterLookup
  exact ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, dts, sts',
    hbefore, hrect, hpos, hi, hsource,
    hafter, hdts, hafterLookup, hprefix, hcLookup⟩

end properties.wasm_module_ok.ValidatedTypeLookup
