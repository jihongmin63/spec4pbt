import properties.wasm_module_ok.ValidatedMatchExistsSearch
import properties.wasm_module_ok.ValidatedMatchDeftypeNeq

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchIndexResult

open properties.wasm_module_ok.ValidatedMatchIndexFuel
open properties.wasm_module_not_ok.Rejection

private theorem deftype_result_iff_of_eval
    (c : SpecTec.context) (dtP dtQ : SpecTec.deftype)
    (start : Nat) (expected result : Bool)
    (hgood : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
      start (.success (.of expected)) start) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
      start (.success (.of result)) start ↔
    result = expected := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, _⟩ := SpecTecExecution.eval_deterministic hdet h hgood
    cases hout
    rfl
  · intro heq
    subst result
    exact hgood

private theorem validated_match_index_result_iff_fixed_target
    (c : SpecTec.context) (q start : Nat)
    (dtQ : SpecTec.deftype)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hq : q < c.TYPES.length)
    (hQ : c.TYPES[q]? = some dtQ) :
    ∀ p dtP, p < c.TYPES.length → c.TYPES[p]? = some dtP →
      ∀ result : Bool,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool,
            SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
          start (.success (.of result)) start ↔
        result = matchIndex c p q := by
  intro p
  induction p using Nat.strongRecOn with
  | ind p ih =>
      intro dtP hp hP result
      have hIH : ∀ k dt, k < p → c.TYPES[k]? = some dt →
          ∀ r : Bool,
            SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨Bool,
                SpecTec.SpecTecCall.«$match_deftype» c.TYPES dt dtQ⟩)
              start (.success (.of r)) start ↔
            r = matchIndex c k q := by
        intro k dt hk hlookup r
        exact ih k hk dt (by omega) hlookup r
      by_cases heq : dtP = dtQ
      · subst dtQ
        have hvalue : matchIndex c p q = true := by
          change matchIndexFuel c (p + 1) p q = true
          exact matchIndexFuel_equal c p p q dtP hP hQ
        rw [hvalue]
        exact deftype_result_iff_of_eval c dtP dtP start true result
          (MatchHeaptypeBasic.match_deftype_refl_total c.TYPES dtP start)
      · obtain ⟨dtP', fin, hts, strt, hP', hunroll, _hedges⟩ :=
          ValidatedUnrolledPredecessors.validated_type_unrolled_predecessors
            c p hc hp
        have hdt : dtP' = dtP := Option.some.inj (hP'.symm.trans hP)
        subst dtP'
        have hexists :=
          ValidatedMatchExistsSearch.validated_match_heaptype_exists_search
            c p q start dtP dtQ fin hts strt hc hp hq hP hQ
            hunroll hIH
        have hunrollEval :=
          (UnrollInterface.unrolldt_success_iff
            dtP (.SubT fin hts strt) start start).2 ⟨hunroll, rfl⟩
        have hmatch :=
          ValidatedMatchDeftypeNeq.validated_match_deftype_neq_of_exists
            c p q start dtP dtQ fin hts strt
            (hts.any (ValidatedMatchExistsSearch.headSearch c p q))
            hc hp hq hP hQ heq hunrollEval hexists
        have hvalue : matchIndex c p q =
            hts.any (ValidatedMatchExistsSearch.headSearch c p q) := by
          simp [matchIndex, matchIndexFuel, hP, hQ, heq, hunroll]
          rfl
        rw [hvalue]
        exact deftype_result_iff_of_eval c dtP dtQ start
          (hts.any (ValidatedMatchExistsSearch.headSearch c p q))
          result hmatch

theorem validated_match_index_result_iff
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype) (result : Bool)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtP dtQ⟩)
      start (.success (.of result)) start ↔
    result = matchIndex c p q :=
  validated_match_index_result_iff_fixed_target
    c q start dtQ hc hq hQ p dtP hp hP result

end properties.wasm_module_ok.ValidatedMatchIndexResult
