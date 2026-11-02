import properties.wasm_module_ok.ValidatedMatchPredecessorSearch
import properties.wasm_module_ok.ValidatedMatchDeftypeTotal

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchDuplicate

open properties.wasm_module_ok.ValidatedMatchIndexFuel

theorem validated_match_index_same_value
    (c : SpecTec.context) (p q start : Nat)
    (dtQ : SpecTec.deftype)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p ≤ c.TYPES.length)
    (hq : q < c.TYPES.length)
    (hQ : c.TYPES[q]? = some dtQ)
    (hIH : ∀ k dtK, k < p → c.TYPES[k]? = some dtK →
      ∀ result : Bool,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Bool,
            SpecTec.SpecTecCall.«$match_deftype» c.TYPES dtK dtQ⟩)
          start (.success (.of result)) start ↔
        result = matchIndex c k q)
    (k₁ k₂ : Nat) (dtK : SpecTec.deftype)
    (hk₁ : k₁ < p) (hk₂ : k₂ < p)
    (h₁ : c.TYPES[k₁]? = some dtK)
    (h₂ : c.TYPES[k₂]? = some dtK) :
    matchIndex c k₁ q = matchIndex c k₂ q := by
  have hk₁Len : k₁ < c.TYPES.length := by omega
  obtain ⟨r, heval⟩ :=
    ValidatedMatchDeftypeTotal.validated_match_deftype_total
      c k₁ q start dtK dtQ hc hk₁Len hq h₁ hQ
  have hr₁ := (hIH k₁ dtK hk₁ h₁ r).1 heval
  have hr₂ := (hIH k₂ dtK hk₂ h₂ r).1 heval
  exact hr₁.symm.trans hr₂

end properties.wasm_module_ok.ValidatedMatchDuplicate
