import properties.wasm_module_ok.ValidatedMatchDeftypeResult
import properties.wasm_module_ok.ValidatedMatchDeftypeTotal

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchHeaptypeResult

theorem validated_match_heaptype_def_pair_result_iff
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
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
      start (.success (.of result)) start := by
  constructor
  · intro hheap
    obtain ⟨r, hdeftype⟩ :=
      ValidatedMatchDeftypeTotal.validated_match_deftype_total
        c p q start dtP dtQ hc hp hq hP hQ
    have hheap' := MatchHeaptypeBasic.match_heaptype_def_def_total_of_match_deftype
      c.TYPES dtP dtQ r start hdeftype
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, _⟩ := SpecTecExecution.eval_deterministic hdet hheap hheap'
    cases hout
    exact hdeftype
  · intro hdeftype
    exact MatchHeaptypeBasic.match_heaptype_def_def_total_of_match_deftype
      c.TYPES dtP dtQ result start hdeftype

theorem validated_match_heaptype_def_pair_classification
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
  exact (validated_match_heaptype_def_pair_result_iff
    c p q start dtP dtQ result hc hp hq hP hQ).trans
    (ValidatedMatchDeftypeResult.validated_match_deftype_result_iff
      c p q start dtP dtQ result hc hp hq hP hQ)

end properties.wasm_module_ok.ValidatedMatchHeaptypeResult
