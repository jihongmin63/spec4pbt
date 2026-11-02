import properties.wasm_module_ok.ValidatedTypeSubstitution
import properties.wasm_module_ok.ValidatedMatchDeftypeInduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchDeftypeTotal

theorem validated_match_deftype_total
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
        start (.success (.of r)) start := by
  have hsubst : ∀ i dt, i < c.TYPES.length → c.TYPES[i]? = some dt →
      ∃ s : SpecTec.deftype,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨SpecTec.deftype,
            SpecTec.SpecTecCall.«$subst_deftype» (List SpecTec.deftype)
              c.TYPES SpecTec.SpecTecCall.«$subst_of» dt⟩)
          start (.success (.of s)) start := by
    intro i dt hi hlookup
    obtain ⟨dt', s, hlookup', hcall⟩ :=
      ValidatedTypeSubstitution.validated_type_substitution_total
        c i start hc hi
    have hdt : dt' = dt := Option.some.inj (hlookup'.symm.trans hlookup)
    subst dt'
    exact ⟨s, hcall⟩
  have hsubstQ := hsubst q dtQ hq hQ
  exact (ValidatedMatchDeftypeInduction.validated_match_deftype_total_of_substitutions
    c dtQ start hc hsubst hsubstQ) p dtP hp hP

end properties.wasm_module_ok.ValidatedMatchDeftypeTotal
