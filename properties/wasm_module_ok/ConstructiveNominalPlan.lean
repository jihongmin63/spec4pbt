import properties.wasm_module_ok.ConstructiveNominalMatch

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveNominalPlan
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ValidatedMatchIndexFuel

/-- Matching is planned from an existing table relation and declared parents,
before any fields are sampled. It never inspects a completed new group. -/
def fuel (old : Nat → Nat → Bool) (base : Nat) (parents : List (Option Nat)) :
    Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | n+1, p, q =>
    if p < base then
      if q < base then old p q else false
    else if p = q then true
    else match parents[p-base]? with
      | some (some parent) => fuel old base parents n parent q
      | _ => false

def matchPlanned (old : Nat → Nat → Bool) (base : Nat) (parents : List (Option Nat))
    (p q : Nat) : Bool := fuel old base parents (p+1) p q

/-- Semantic connection of the planned parent graph to a built type table.
Readiness and these edges must be established structurally by group assembly. -/
def Edges (c : context) (base : Nat) (parents : List (Option Nat)) : Prop :=
  ∀ i parent, parents[i]? = some parent →
    ∃ dt f st, c.TYPES[base+i]? = some dt ∧
      match parent with
      | none => unrollDeftypeResult dt = some (.SubT f [] st)
      | some k => k < base+i ∧ ∃ target, c.TYPES[k]? = some target ∧
          unrollDeftypeResult dt = some (.SubT f [.DefHT target] st)

theorem fuel_sound (before after : context) (tail : List deftype)
    (parents : List (Option Nat)) (hprefix : after.TYPES = before.TYPES ++ tail)
    (hready : CandidateTypeReady.Ready after)
    (hedges : Edges after before.TYPES.length parents)
    (_hlen : tail.length = parents.length)
    (n p q : Nat) (hp : p < after.TYPES.length) (hq : q < after.TYPES.length)
    (h : fuel (matchIndex before) before.TYPES.length parents n p q = true) :
    matchIndex after p q = true := by
  induction n generalizing p q with
  | zero => cases h
  | succ n ih =>
    simp only [fuel] at h
    split at h
    · rename_i hold
      split at h
      · rename_i hqold
        rw [ConstructiveNominalMatch.index_prefix before after tail hprefix p q hold hqold]
        exact h
      · cases h
    · rename_i hnew
      split at h
      · rename_i heq
        subst q
        simp [matchIndex, matchIndexFuel, List.getElem?_eq_getElem hp]
      · rename_i hne
        cases he : parents[p-before.TYPES.length]? with
        | none => simp [he] at h
        | some parent =>
          cases parent with
          | none => simp [he] at h
          | some k =>
            simp only [he] at h
            obtain ⟨dt, f, st, hget, hk, target, htarget, hu⟩ := hedges _ _ he
            have hpos : before.TYPES.length + (p-before.TYPES.length) = p := by omega
            rw [hpos] at hget hk
            have hkb := (List.getElem?_eq_some_iff.mp htarget).1
            have hrec := ih k q hkb hq h
            rw [ConstructiveNominalMatch.single_parent after p q k dt after.TYPES[q]
              target f st hready hget (List.getElem?_eq_getElem hq) htarget hk hu,
              hrec, Bool.or_true]

theorem matches_sound (before after : context) (tail : List deftype)
    (parents : List (Option Nat)) (hprefix : after.TYPES = before.TYPES ++ tail)
    (hready : CandidateTypeReady.Ready after)
    (hedges : Edges after before.TYPES.length parents)
    (hlen : tail.length = parents.length)
    (p q : Nat) (hp : p < after.TYPES.length) (hq : q < after.TYPES.length) :
    matchPlanned (matchIndex before) before.TYPES.length parents p q = true →
      matchIndex after p q = true :=
  fuel_sound before after tail parents hprefix hready hedges hlen (p+1) p q hp hq

/-- Freshness here is a hypothesis of the backward proof only. The generation
path does not test it: accidental equality can only add actual matches. -/
def NoAliases (before after : context) : Prop :=
  ∀ p q, p < after.TYPES.length → q < after.TYPES.length →
    (before.TYPES.length ≤ p ∨ before.TYPES.length ≤ q) →
    after.TYPES[p]? = after.TYPES[q]? → p = q

theorem old_new_false (before after : context) (hno : NoAliases before after)
    (n p q : Nat) (hp : p < before.TYPES.length) (hp' : p < after.TYPES.length)
    (hq : q < after.TYPES.length) (hqnew : before.TYPES.length ≤ q) :
    matchIndexFuel after n p q = false := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    have hne : after.TYPES[p] ≠ after.TYPES[q] := by
      intro he
      have hlookup : after.TYPES[p]? = after.TYPES[q]? := by
        rw [List.getElem?_eq_getElem hp', List.getElem?_eq_getElem hq, he]
      have heq := hno p q hp' hq (Or.inr hqnew) hlookup
      omega
    simp only [matchIndexFuel, List.getElem?_eq_getElem hp',
      List.getElem?_eq_getElem hq, if_neg hne]
    cases unrollDeftypeResult after.TYPES[p] with
    | none => rfl
    | some s =>
      cases s with
      | SubT f ps st =>
        apply List.any_eq_false.mpr
        intro ht hmem
        cases ht <;> try exact Bool.false_ne_true
        rename_i dt
        intro htrue
        obtain ⟨k, hk, hvalue⟩ := List.any_eq_true.mp htrue
        have hkp : k < p := List.mem_range.mp hk
        rw [ih k (Nat.lt_trans hkp hp) (Nat.lt_trans hkp hp')] at hvalue
        simp at hvalue

theorem fuel_exact (before after : context) (tail : List deftype)
    (parents : List (Option Nat)) (hprefix : after.TYPES = before.TYPES ++ tail)
    (hready : CandidateTypeReady.Ready after)
    (hedges : Edges after before.TYPES.length parents)
    (hlen : tail.length = parents.length) (hno : NoAliases before after)
    (n p q : Nat) (hn : p < n)
    (hp : p < after.TYPES.length) (hq : q < after.TYPES.length) :
    fuel (matchIndex before) before.TYPES.length parents n p q = matchIndex after p q := by
  induction n generalizing p q with
  | zero => omega
  | succ n ih =>
    by_cases hold : p < before.TYPES.length
    · by_cases hqold : q < before.TYPES.length
      · simp only [fuel, if_pos hold, if_pos hqold]
        exact (ConstructiveNominalMatch.index_prefix before after tail hprefix p q hold hqold).symm
      · simp only [fuel, if_pos hold, if_neg hqold]
        exact (old_new_false before after hno (p+1) p q hold hp hq (by omega)).symm
    · by_cases heq : p = q
      · subst q
        simp [fuel, hold, matchIndex, matchIndexFuel, List.getElem?_eq_getElem hp]
      · have hi : p - before.TYPES.length < parents.length := by
          have hlength : after.TYPES.length = before.TYPES.length + parents.length := by
            simp [hprefix, hlen]
          omega
        have hpos : before.TYPES.length + (p-before.TYPES.length) = p := by omega
        have he := List.getElem?_eq_getElem hi
        obtain ⟨dt, f, st, hget, hedge⟩ := hedges _ _ he
        rw [hpos] at hget
        have hneq : dt ≠ after.TYPES[q] := by
          intro heqdt
          have hlookup : after.TYPES[p]? = after.TYPES[q]? := by
            rw [hget, List.getElem?_eq_getElem hq, heqdt]
          exact heq (hno p q hp hq (Or.inl (by omega)) hlookup)
        cases hpar : parents[p-before.TYPES.length] with
        | none =>
          rw [hpar] at he hedge
          simp only [fuel, if_neg hold, if_neg heq, he]
          rw [ConstructiveNominalMatch.root after p q dt after.TYPES[q] f st
            hget (List.getElem?_eq_getElem hq) hedge, decide_eq_false hneq]
        | some k =>
          rw [hpar] at he hedge
          obtain ⟨hk, target, htarget, hu⟩ := hedge
          rw [hpos] at hk
          have hkb := (List.getElem?_eq_some_iff.mp htarget).1
          simp only [fuel, if_neg hold, if_neg heq, he]
          rw [ConstructiveNominalMatch.single_parent after p q k dt after.TYPES[q]
            target f st hready hget (List.getElem?_eq_getElem hq) htarget hk hu,
            decide_eq_false hneq, Bool.false_or]
          exact ih k q (by omega) hkb hq

theorem planned_exact (before after : context) (tail : List deftype)
    (parents : List (Option Nat)) (hprefix : after.TYPES = before.TYPES ++ tail)
    (hready : CandidateTypeReady.Ready after)
    (hedges : Edges after before.TYPES.length parents)
    (hlen : tail.length = parents.length) (hno : NoAliases before after)
    (p q : Nat) (hp : p < after.TYPES.length) (hq : q < after.TYPES.length) :
    matchPlanned (matchIndex before) before.TYPES.length parents p q = matchIndex after p q :=
  fuel_exact before after tail parents hprefix hready hedges hlen hno (p+1) p q
    (Nat.lt_succ_self p) hp hq

theorem fresh_no_aliases (before after : context) (rt : rectype) (width : Nat)
    (hprefix : after.TYPES = before.TYPES ++
      (List.range width).map (fun i => deftype.DefT rt i))
    (hfresh : ∀ p i : Nat, before.TYPES[p]? ≠ some (deftype.DefT rt i)) : NoAliases before after := by
  have hnew : ∀ p, before.TYPES.length ≤ p → p < after.TYPES.length →
      after.TYPES[p]? = some (.DefT rt (p-before.TYPES.length)) := by
    intro p hp hpbound
    have hlen : after.TYPES.length = before.TYPES.length + width := by simp [hprefix]
    have hi : p-before.TYPES.length < width := by omega
    simp [hprefix, List.getElem?_append_right hp, List.getElem?_map, hi]
  intro p q hp hq hnewside heq
  by_cases hpold : p < before.TYPES.length
  · have hqnew : before.TYPES.length ≤ q := by omega
    have hpget : after.TYPES[p]? = before.TYPES[p]? := by
      simp [hprefix, List.getElem?_append_left hpold]
    rw [hpget, hnew q hqnew hq] at heq
    exact False.elim (hfresh p _ heq)
  · have hpnew : before.TYPES.length ≤ p := by omega
    by_cases hqold : q < before.TYPES.length
    · have hqget : after.TYPES[q]? = before.TYPES[q]? := by
        simp [hprefix, List.getElem?_append_left hqold]
      rw [hqget, hnew p hpnew hp] at heq
      exact False.elim (hfresh q _ heq.symm)
    · have hqnew : before.TYPES.length ≤ q := by omega
      rw [hnew p hpnew hp, hnew q hqnew hq] at heq
      have hdiff : p-before.TYPES.length = q-before.TYPES.length :=
        deftype.DefT.inj (Option.some.inj heq) |>.2
      calc
        p = (p-before.TYPES.length) + before.TYPES.length := (Nat.sub_add_cancel hpnew).symm
        _ = (q-before.TYPES.length) + before.TYPES.length := congrArg (· + before.TYPES.length) hdiff
        _ = q := Nat.sub_add_cancel hqnew

end properties.wasm_module_ok.ConstructiveNominalPlan
