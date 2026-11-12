import properties.wasm_module_ok.ValidatedUnrolledPredecessors

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedMatchIndexFuel

open properties.wasm_module_not_ok.Rejection

/-- A finite, executable search over earlier type positions. For validated type
entries, every unrolled supertype is represented at an earlier position. The
semantic correspondence to translated matching is proved separately. -/
def matchIndexFuel (c : SpecTec.context) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, p, q =>
      match c.TYPES[p]?, c.TYPES[q]? with
      | some dtP, some dtQ =>
          if dtP = dtQ then true
          else
            match unrollDeftypeResult dtP with
            | some (.SubT _ hts _) =>
                hts.any fun ht =>
                  match ht with
                  | .DefHT dtK =>
                      (List.range p).any fun k =>
                        decide (c.TYPES[k]? = some dtK) &&
                          matchIndexFuel c fuel k q
                  | _ => false
            | none => false
      | _, _ => false

/-- The source index itself provides enough search depth for validated entries,
because every recursive predecessor index is strictly smaller. -/
def matchIndex (c : SpecTec.context) (p q : Nat) : Bool :=
  matchIndexFuel c (p + 1) p q

theorem matchIndexFuel_zero (c : SpecTec.context) (p q : Nat) :
    matchIndexFuel c 0 p q = false := rfl

theorem matchIndexFuel_equal
    (c : SpecTec.context) (fuel p q : Nat)
    (dt : SpecTec.deftype)
    (hp : c.TYPES[p]? = some dt)
    (hq : c.TYPES[q]? = some dt) :
    matchIndexFuel c (fuel + 1) p q = true := by
  simp [matchIndexFuel, hp, hq]

theorem predecessor_search_true_iff
    (c : SpecTec.context) (fuel p q : Nat)
    (dtK : SpecTec.deftype) :
    ((List.range p).any fun k =>
      decide (c.TYPES[k]? = some dtK) && matchIndexFuel c fuel k q) = true ↔
    ∃ k : Nat, k < p ∧ c.TYPES[k]? = some dtK ∧
      matchIndexFuel c fuel k q = true := by
  simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]

end properties.wasm_module_ok.ValidatedMatchIndexFuel
