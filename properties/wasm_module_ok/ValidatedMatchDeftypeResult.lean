import properties.wasm_module_ok.ValidatedMatchDeftypeNeq
import properties.wasm_module_ok.ValidatedTypeMatchExistsTotal

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchDeftypeResult

theorem validated_match_deftype_result_iff
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype) (result : Bool)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
      start (.success (.of result)) start ↔
    (dtP = dtQ ∧ result = true) ∨
    (dtP ≠ dtQ ∧ ∃ fin : SpecTec.final,
      ∃ hts : List SpecTec.heaptype,
      ∃ strt : SpecTec.strtype,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dtP⟩)
          start (.success (.of (SpecTec.subtype.SubT fin hts strt))) start ∧
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool,
            SpecTec.SpecTecCall.«$match_heaptype_exists» c.TYPES hts dtQ⟩)
          start (.success (.of result)) start) := by
  have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request x y hp
    cases hp
  constructor
  · intro hmatch
    by_cases heq : dtP = dtQ
    · left
      subst dtQ
      have href := MatchHeaptypeBasic.match_deftype_refl_total c.TYPES dtP start
      obtain ⟨hout, _⟩ := SpecTecExecution.eval_deterministic hdet hmatch href
      cases hout
      exact ⟨rfl, rfl⟩
    · right
      obtain ⟨dtP', dtQ', fin, hts, strt, r, hP', hQ', hunroll, hexists⟩ :=
        ValidatedTypeMatchExistsTotal.validated_type_match_exists_total
          c p q start hc hp hq
      have hpEq : dtP' = dtP := Option.some.inj (hP'.symm.trans hP)
      have hqEq : dtQ' = dtQ := Option.some.inj (hQ'.symm.trans hQ)
      subst dtP'
      subst dtQ'
      have hbranch :=
        ValidatedMatchDeftypeNeq.validated_match_deftype_neq_of_exists
          c p q start dtP dtQ fin hts strt r hc hp hq hP hQ heq
          hunroll hexists
      obtain ⟨hout, _⟩ := SpecTecExecution.eval_deterministic hdet hmatch hbranch
      cases hout
      exact ⟨heq, fin, hts, strt, hunroll, hexists⟩
  · rintro (⟨heq, rfl⟩ | ⟨hne, fin, hts, strt, hunroll, hexists⟩)
    · subst dtQ
      exact MatchHeaptypeBasic.match_deftype_refl_total c.TYPES dtP start
    · exact ValidatedMatchDeftypeNeq.validated_match_deftype_neq_of_exists
        c p q start dtP dtQ fin hts strt result hc hp hq hP hQ hne
        hunroll hexists

end properties.wasm_module_ok.ValidatedMatchDeftypeResult
