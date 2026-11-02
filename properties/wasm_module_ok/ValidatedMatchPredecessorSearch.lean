import properties.wasm_module_ok.ValidatedMatchFuelBound

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchPredecessorSearch

open properties.wasm_module_ok.ValidatedMatchIndexFuel

theorem predecessor_search_eq_of_constant
    (c : SpecTec.context) (fuel p q : Nat)
    (dtK : SpecTec.deftype) (r : Bool)
    (hwitness : ∃ k : Nat, k < p ∧ c.TYPES[k]? = some dtK)
    (hconstant : ∀ k : Nat, k < p → c.TYPES[k]? = some dtK →
      matchIndexFuel c fuel k q = r) :
    ((List.range p).any fun k =>
      decide (c.TYPES[k]? = some dtK) && matchIndexFuel c fuel k q) = r := by
  cases r with
  | true =>
      obtain ⟨k, hk, hlookup⟩ := hwitness
      exact (predecessor_search_true_iff c fuel p q dtK).2
        ⟨k, hk, hlookup, hconstant k hk hlookup⟩
  | false =>
      cases hsearch : (List.range p).any (fun k =>
          decide (c.TYPES[k]? = some dtK) && matchIndexFuel c fuel k q) with
      | false => rfl
      | true =>
          obtain ⟨k, hk, hlookup, htrue⟩ :=
            (predecessor_search_true_iff c fuel p q dtK).1 hsearch
          have hfalse := hconstant k hk hlookup
          rw [hfalse] at htrue
          cases htrue

end properties.wasm_module_ok.ValidatedMatchPredecessorSearch
