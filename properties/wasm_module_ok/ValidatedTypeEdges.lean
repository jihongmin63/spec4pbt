import properties.wasm_module_ok.ValidatedTypeChain
import properties.wasm_module_ok.ActualAllSupertypeCases

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedTypeEdges

open properties.wasm_module_ok.ValidatedTypeChain

theorem validated_types_position_edges
    (c : SpecTec.context) (p : Nat)
    (hc : ValidatedTypes c) (hp : p < c.TYPES.length) :
    ∃ before after : SpecTec.context,
    ∃ sts : List SpecTec.subtype,
    ∃ start finish i : Nat,
    ∃ tail : List SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strt : SpecTec.strtype,
      ValidatedTypes before ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
        start (.success (.of after)) finish ∧
      p = before.TYPES.length + i ∧ i < sts.length ∧
      sts[i]? = some (.SubT fin hts strt) ∧
      c.TYPES = after.TYPES ++ tail ∧
      ∀ j, j < hts.length →
        ∃ k : Nat,
          hts[j]? = some (.VarHT (.StatX k)) ∧
          k < before.TYPES.length + i ∧
          ∃ dts : List SpecTec.deftype,
          ∃ sts' : List SpecTec.subtype,
          ∃ hts' : List SpecTec.heaptype,
          ∃ strt' : SpecTec.strtype,
            after = {before with TYPES := before.TYPES ++ dts} ∧
            dts[i]? = some (.DefT (.RecT sts') i) ∧
            sts'[i]? = some (.SubT fin hts' strt') ∧
            ((∃ dt : SpecTec.deftype,
                k < before.TYPES.length ∧ before.TYPES[k]? = some dt ∧
                hts'[j]? = some (.DefHT dt)) ∨
              (before.TYPES.length ≤ k ∧ k - before.TYPES.length < i ∧
                hts'[j]? = some (.VarHT (.RecX (k - before.TYPES.length))))) := by
  obtain ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, hbefore, hrect, hpos, hi, hsource, hprefix⟩ :=
    validated_types_position_source c p hc hp
  refine ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, hbefore, hrect, hpos, hi, hsource, hprefix, ?_⟩
  intro j hj
  exact ActualAllSupertypeCases.rectype_ok_appended_all_supertype_cases
    before after sts start finish i j fin hts strt
    hrect hi hsource hj

end properties.wasm_module_ok.ValidatedTypeEdges
