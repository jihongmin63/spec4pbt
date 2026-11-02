import properties.wasm_module_ok.ValidatedMatchExistsBridge

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchDeftypeStep

open properties.wasm_module_ok.ValidatedTypeChain

theorem validated_match_deftype_of_predecessors
    (c : SpecTec.context) (p : Nat)
    (dtP dtQ : SpecTec.deftype) (start : Nat)
    (hc : ValidatedTypes c) (hp : p < c.TYPES.length)
    (hlookup : c.TYPES[p]? = some dtP)
    (hsubstP : ∃ sP : SpecTec.deftype,
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
        start (.success (.of sQ)) start)
    (hmatch : ∀ k dtK, k < p → c.TYPES[k]? = some dtK →
      ∃ r : Bool,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool,
            SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtK dtQ⟩)
          start (.success (.of r)) start) :
    ∃ r : Bool,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
        start (.success (.of r)) start := by
  by_cases heq : dtP = dtQ
  · subst dtQ
    exact ⟨true,
      MatchHeaptypeBasic.match_deftype_refl_total c.TYPES dtP start⟩
  obtain ⟨sP, hsP⟩ := hsubstP
  obtain ⟨sQ, hsQ⟩ := hsubstQ
  by_cases hsEq : sP = sQ
  · subst sQ
    exact ⟨true,
      MatchHeaptypeBasic.match_deftype_neq_subst_eq_total
        c.TYPES dtP dtQ sP start heq hsP hsQ⟩
  obtain ⟨dtP', fin, htsU, strtU, r,
    hlookup', hunroll, hexists⟩ :=
    ValidatedMatchExistsBridge.validated_type_match_exists_of_predecessors
      c p dtQ start hc hp hmatch
  have hdtEq : dtP' = dtP :=
    Option.some.inj (hlookup'.symm.trans hlookup)
  subst dtP'
  exact ⟨r,
    MatchHeaptypeBasic.match_deftype_neq_subst_neq_total_of_exists
      c.TYPES dtP dtQ sP sQ fin htsU strtU r start
      heq hsP hsQ hsEq hunroll hexists⟩

end properties.wasm_module_ok.ValidatedMatchDeftypeStep
