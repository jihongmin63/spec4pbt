import properties.wasm_module_ok.ReadyMatchDefHeadSearch
import properties.wasm_module_ok.ReadyTypeInterfaces
import properties.wasm_module_ok.MatchHeaptypeExistsResult

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyMatchExistsSearch

open properties.wasm_module_ok.ValidatedMatchIndexFuel
open properties.wasm_module_not_ok.Rejection

def headSearch (c : SpecTec.context) (p q : Nat) :
    SpecTec.heaptype → Bool
  | .DefHT dtK =>
      (List.range p).any fun k =>
        decide (c.TYPES[k]? = some dtK) &&
          matchIndexFuel c p k q
  | _ => false

theorem ready_match_heaptype_exists_search
    (c : SpecTec.context) (p q start : Nat)
    (dtP dtQ : SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p < c.TYPES.length) (hq : q < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hQ : c.TYPES[q]? = some dtQ)
    (hunroll : unrollDeftypeResult dtP = some (.SubT fin hts strt))
    (hIH : ∀ k dt, k < p → c.TYPES[k]? = some dt →
      ∀ r : Bool,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool,
            SpecTec.SpecTecCall.«$match_deftype» c.TYPES dt dtQ⟩)
          start (.success (.of r)) start ↔
        r = matchIndex c k q) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype_exists» c.TYPES hts dtQ⟩)
      start (.success (.of (hts.any (headSearch c p q)))) start := by
  have hedges :=
    ReadyTypeInterfaces.ready_unrolled_supertype_member_for_result
      c hready p dtP fin hts strt hp hP hunroll
  apply MatchHeaptypeExistsResult.match_heaptype_exists_result_of_head_classifier
    c.TYPES dtQ hts (headSearch c p q) start
  intro ht hmem
  obtain ⟨k, dtK, hk, hlookup, heq⟩ := hedges ht hmem
  subst ht
  simpa [headSearch] using
    (ReadyMatchDefHeadSearch.ready_def_head_matches_predecessor_search
      c p q start dtQ dtK hready (by omega) hq hQ hIH
      ⟨k, hk, hlookup⟩)

end properties.wasm_module_ok.ReadyMatchExistsSearch
