import properties.wasm_module_ok.ValidatedMatchIndexFuel

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchFuelBound

open properties.wasm_module_ok.ValidatedMatchIndexFuel
open properties.wasm_module_not_ok.Rejection

private theorem any_congr_on_members
    {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp [List.any, hx, ih hxs]

theorem matchIndexFuel_stable_of_gt
    (c : SpecTec.context) (p q f g : Nat)
    (hf : p < f) (hg : p < g) :
    matchIndexFuel c f p q = matchIndexFuel c g p q := by
  induction p using Nat.strongRecOn generalizing q f g with
  | ind p ih =>
      cases f with
      | zero => omega
      | succ f =>
          cases g with
          | zero => omega
          | succ g =>
              cases hpLookup : c.TYPES[p]? with
              | none => simp [matchIndexFuel, hpLookup]
              | some dtP =>
                  cases hqLookup : c.TYPES[q]? with
                  | none => simp [matchIndexFuel, hpLookup, hqLookup]
                  | some dtQ =>
                      by_cases heq : dtP = dtQ
                      · simp [matchIndexFuel, hpLookup, hqLookup, heq]
                      · cases hu : unrollDeftypeResult dtP with
                        | none =>
                            simp [matchIndexFuel, hpLookup, hqLookup, heq, hu]
                        | some st =>
                            cases st with
                            | SubT fin hts strt =>
                                simp only [matchIndexFuel, hpLookup, hqLookup,
                                  if_neg heq, hu]
                                apply any_congr_on_members
                                intro ht hmem
                                cases ht <;> try rfl
                                case DefHT dtK =>
                                  apply any_congr_on_members
                                  intro k hk
                                  have hkp : k < p := List.mem_range.mp hk
                                  have hkf : k < f := by omega
                                  have hkg : k < g := by omega
                                  rw [ih k hkp q f g hkf hkg]

theorem matchIndexFuel_eq_matchIndex
    (c : SpecTec.context) (p q fuel : Nat)
    (hf : p < fuel) :
    matchIndexFuel c fuel p q = matchIndex c p q := by
  exact matchIndexFuel_stable_of_gt c p q fuel (p + 1) hf (by omega)

end properties.wasm_module_ok.ValidatedMatchFuelBound
