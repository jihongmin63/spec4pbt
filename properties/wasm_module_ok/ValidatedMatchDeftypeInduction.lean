import properties.wasm_module_ok.ValidatedMatchDeftypeStep

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchDeftypeInduction

open properties.wasm_module_ok.ValidatedTypeChain

theorem validated_match_deftype_total_of_substitutions
    (c : SpecTec.context) (dtQ : SpecTec.deftype)
    (start : Nat) (hc : ValidatedTypes c)
    (hsubst : ∀ p dtP, p < c.TYPES.length → c.TYPES[p]? = some dtP →
      ∃ sP : SpecTec.deftype,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨SpecTec.deftype,
            SpecTec.SpecTecCall.«$subst_deftype» (List SpecTec.deftype)
              c.TYPES SpecTec.SpecTecCall.«$subst_of» dtP⟩)
          start (.success (.of sP)) start)
    (hsubstQ : ∃ sQ : SpecTec.deftype,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.deftype,
          SpecTec.SpecTecCall.«$subst_deftype» (List SpecTec.deftype)
            c.TYPES SpecTec.SpecTecCall.«$subst_of» dtQ⟩)
        start (.success (.of sQ)) start) :
    ∀ p dtP, p < c.TYPES.length → c.TYPES[p]? = some dtP →
      ∃ r : Bool,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool,
            SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
          start (.success (.of r)) start := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
      intro dtP hp hlookup
      apply ValidatedMatchDeftypeStep.validated_match_deftype_of_predecessors
        c p dtP dtQ start hc hp hlookup (hsubst p dtP hp hlookup)
        hsubstQ
      intro k dtK hkp hkLookup
      have hk : k < c.TYPES.length := by omega
      exact ih k hkp dtK hk hkLookup

end properties.wasm_module_ok.ValidatedMatchDeftypeInduction
