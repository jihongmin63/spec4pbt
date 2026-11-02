import properties.wasm_module_ok.ValidatedTypeSubstitution
import properties.wasm_module_ok.MatchHeaptypeBasic

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchDeftypeNeq

theorem validated_match_deftype_neq_of_exists
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (r : Bool)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ)
    (hne : dtP ≠ dtQ)
    (hunroll : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dtP⟩)
      start (.success (.of (SpecTec.subtype.SubT fin hts strt))) start)
    (hexists : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» c.TYPES hts dtQ⟩)
      start (.success (.of r)) start) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
      start (.success (.of r)) start := by
  have hsubstP :=
    ValidatedTypeSubstitution.validated_type_substitution_fixed
      c p start dtP hc hp hP
  have hsubstQ :=
    ValidatedTypeSubstitution.validated_type_substitution_fixed
      c q start dtQ hc hq hQ
  exact MatchHeaptypeBasic.match_deftype_neq_subst_neq_total_of_exists
    c.TYPES dtP dtQ dtP dtQ fin hts strt r start
    hne hsubstP hsubstQ hne hunroll hexists

end properties.wasm_module_ok.ValidatedMatchDeftypeNeq
