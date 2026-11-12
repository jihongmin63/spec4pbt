import properties.wasm_module_ok.ReadyMatchTotal
import properties.wasm_module_ok.ValidatedMatchPredecessorSearch

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyMatchDefHeadSearch

open properties.wasm_module_ok.ValidatedMatchIndexFuel

private theorem ready_match_index_same_value
    (c : SpecTec.context) (p q start : Nat)
    (dtQ : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p ≤ c.TYPES.length)
    (hq : q < c.TYPES.length)
    (hQ : c.TYPES[q]? = some dtQ)
    (hIH : ∀ k dtK, k < p → c.TYPES[k]? = some dtK →
      ∀ result : Bool,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Bool,
            SpecTec.Call.«$match_deftype» c.TYPES dtK dtQ⟩)
          start (.success (.of result)) start ↔
        result = matchIndex c k q)
    (k₁ k₂ : Nat) (dtK : SpecTec.deftype)
    (hk₁ : k₁ < p) (hk₂ : k₂ < p)
    (h₁ : c.TYPES[k₁]? = some dtK)
    (h₂ : c.TYPES[k₂]? = some dtK) :
    matchIndex c k₁ q = matchIndex c k₂ q := by
  have hk₁Len : k₁ < c.TYPES.length := by omega
  obtain ⟨r, heval⟩ :=
    ReadyMatchTotal.ready_match_deftype_total
      c k₁ q start dtK dtQ hready hk₁Len hq h₁ hQ
  have hr₁ := (hIH k₁ dtK hk₁ h₁ r).1 heval
  have hr₂ := (hIH k₂ dtK hk₂ h₂ r).1 heval
  exact hr₁.symm.trans hr₂

theorem ready_def_head_matches_predecessor_search
    (c : SpecTec.context) (p q start : Nat)
    (dtQ dtK : SpecTec.deftype)
    (hready : CandidateTypeReady.Ready c)
    (hp : p ≤ c.TYPES.length) (hq : q < c.TYPES.length)
    (hQ : c.TYPES[q]? = some dtQ)
    (hIH : ∀ k dt, k < p → c.TYPES[k]? = some dt →
      ∀ r : Bool,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Bool,
            SpecTec.Call.«$match_deftype» c.TYPES dt dtQ⟩)
          start (.success (.of r)) start ↔
        r = matchIndex c k q)
    (hwitness : ∃ k : Nat, k < p ∧ c.TYPES[k]? = some dtK) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_heaptype» c.TYPES
          (.DefHT dtK) (.DefHT dtQ)⟩)
      start (.success (.of
        ((List.range p).any fun k =>
          decide (c.TYPES[k]? = some dtK) &&
            matchIndexFuel c p k q))) start := by
  obtain ⟨k₀, hk₀, hlookup₀⟩ := hwitness
  have hk₀Len : k₀ < c.TYPES.length := by omega
  obtain ⟨r, hmatch⟩ :=
    ReadyMatchTotal.ready_match_deftype_total
      c k₀ q start dtK dtQ hready hk₀Len hq hlookup₀ hQ
  have hr₀ : r = matchIndex c k₀ q :=
    (hIH k₀ dtK hk₀ hlookup₀ r).1 hmatch
  have hconstant : ∀ k : Nat, k < p → c.TYPES[k]? = some dtK →
      matchIndexFuel c p k q = r := by
    intro k hk hlookup
    rw [ValidatedMatchFuelBound.matchIndexFuel_eq_matchIndex c k q p hk]
    have hsame := ready_match_index_same_value
      c p q start dtQ hready hp hq hQ hIH
      k k₀ dtK hk hk₀ hlookup hlookup₀
    exact hsame.trans hr₀.symm
  have hsearch :=
    ValidatedMatchPredecessorSearch.predecessor_search_eq_of_constant
      c p p q dtK r ⟨k₀, hk₀, hlookup₀⟩ hconstant
  rw [hsearch]
  exact MatchHeaptypeBasic.match_heaptype_def_def_total_of_match_deftype
    c.TYPES dtK dtQ r start hmatch

end properties.wasm_module_ok.ReadyMatchDefHeadSearch
