import properties.wasm_module_ok.ReadyMatchHeaptypeIndex
import properties.wasm_module_ok.ValidatedMatchPredecessorSearch

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveNominalMatch
open SpecTec SpecTecExecution properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ValidatedMatchIndexFuel

theorem single_parent (c : context) (p q parent : Nat)
    (source target ancestor : deftype) (fin : SpecTec.final) (st : strtype)
    (hready : CandidateTypeReady.Ready c)
    (hp : c.TYPES[p]? = some source) (hq : c.TYPES[q]? = some target)
    (ha : c.TYPES[parent]? = some ancestor) (hlt : parent < p)
    (hu : unrollDeftypeResult source = some (.SubT fin [.DefHT ancestor] st)) :
    matchIndex c p q = (decide (source = target) || matchIndex c parent q) := by
  by_cases heq : source = target
  · simp [matchIndex, matchIndexFuel, hp, hq, heq]
  · have hs : matchIndex c p q = ((List.range p).any fun k =>
        decide (c.TYPES[k]? = some ancestor) && matchIndexFuel c p k q) := by
      simp only [matchIndex, matchIndexFuel, hp, hq, if_neg heq, hu,
        List.any_cons, List.any_nil, Bool.or_false]
    rw [hs, decide_eq_false heq, Bool.false_or]
    apply ValidatedMatchPredecessorSearch.predecessor_search_eq_of_constant
      c p p q ancestor (matchIndex c parent q) ⟨parent, hlt, ha⟩
    intro k hkp hk
    rw [ValidatedMatchFuelBound.matchIndexFuel_eq_matchIndex c k q p hkp]
    exact ReadyMatchHeaptypeIndex.ready_match_index_same_values c k parent q q 0
      ancestor target hready
      (List.getElem?_eq_some_iff.mp hk).1 (List.getElem?_eq_some_iff.mp ha).1
      (List.getElem?_eq_some_iff.mp hq).1 (List.getElem?_eq_some_iff.mp hq).1
      hk ha hq hq

theorem root (c : context) (p q : Nat)
    (source target : deftype) (fin : SpecTec.final) (st : strtype)
    (hp : c.TYPES[p]? = some source) (hq : c.TYPES[q]? = some target)
    (hu : unrollDeftypeResult source = some (.SubT fin [] st)) :
    matchIndex c p q = decide (source = target) := by
  by_cases heq : source = target <;> simp [matchIndex, matchIndexFuel, hp, hq, heq, hu]

/-- Equality of closed definitions forces equality of the whole recursive group
and the entry position, not merely equality of expanded structural shapes. -/
theorem closed_definition_eq (a b : rectype) (i j : Nat) :
    deftype.DefT a i = deftype.DefT b j ↔ a = b ∧ i = j := by
  simp only [deftype.DefT.injEq]


theorem single_parent_original (c : context) (p q parent : Nat)
    (source target ancestor : deftype) (fin : SpecTec.final) (st : strtype)
    (hready : CandidateTypeReady.Ready c)
    (hp : c.TYPES[p]? = some source) (hq : c.TYPES[q]? = some target)
    (ha : c.TYPES[parent]? = some ancestor) (hlt : parent < p)
    (hu : unrollDeftypeResult source = some (.SubT fin [.DefHT ancestor] st))
    (n : Nat) :
    Eval specTecProgram (.call ⟨Bool, SpecTecCall.«$match_heaptype» c.TYPES
      (.DefHT source) (.DefHT target)⟩)
      n (.success (.of (decide (source = target) || matchIndex c parent q))) n := by
  have h := ReadyMatchHeaptypeIndex.ready_match_heaptype_def_pair_total c p q n source target
    hready (List.getElem?_eq_some_iff.mp hp).1 (List.getElem?_eq_some_iff.mp hq).1 hp hq
  rw [single_parent c p q parent source target ancestor fin st hready hp hq ha hlt hu] at h
  exact h

private theorem any_congr_mem {α : Type} (xs : List α) (f g : α → Bool)
    (h : ∀ x ∈ xs, f x = g x) : xs.any f = xs.any g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem fuel_prefix (before after : context) (tail : List deftype)
    (h : after.TYPES = before.TYPES ++ tail) (fuel p q : Nat)
    (hp : p < before.TYPES.length) (hq : q < before.TYPES.length) :
    matchIndexFuel after fuel p q = matchIndexFuel before fuel p q := by
  induction fuel generalizing p q with
  | zero => rfl
  | succ fuel ih =>
    simp only [matchIndexFuel, h, List.getElem?_append_left hp, List.getElem?_append_left hq]
    cases before.TYPES[p]? <;> cases before.TYPES[q]?
    all_goals try rfl
    rename_i dtP dtQ
    by_cases he : dtP = dtQ
    · simp [he]
    · simp only [if_neg he]
      cases unrollDeftypeResult dtP with
      | none => rfl
      | some st =>
        cases st with
        | SubT fin hts st =>
          apply List.any_congr rfl
          intro ht
          cases ht <;> try rfl
          rename_i dtK
          apply any_congr_mem
          intro k hk
          have hkp : k < p := List.mem_range.mp hk
          have hkb : k < before.TYPES.length := Nat.lt_trans hkp hp
          rw [List.getElem?_append_left hkb, ih k q hkb hq]


theorem index_prefix (before after : context) (tail : List deftype)
    (h : after.TYPES = before.TYPES ++ tail) (p q : Nat)
    (hp : p < before.TYPES.length) (hq : q < before.TYPES.length) :
    matchIndex after p q = matchIndex before p q :=
  fuel_prefix before after tail h (p + 1) p q hp hq

end properties.wasm_module_ok.ConstructiveNominalMatch
