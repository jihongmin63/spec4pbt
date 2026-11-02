import properties.wasm_module_ok.ConstructiveTypeClosed
import properties.wasm_module_ok.ConstructiveNominalPlan
import properties.wasm_module_ok.CandidateTypeReadyExtension
import properties.wasm_module_ok.UnrollPositionBridge

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeEnvironment
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ConstructiveTypeCopy ConstructiveTypeCopySemantics

def definitions (rt : rectype) (width : Nat) : List deftype :=
  (List.range width).map (fun i => .DefT rt i)

def extended (c : context) (sts : List SpecTec.subtype)
    (h : GroupBound (c.TYPES.length+sts.length) sts) : context :=
  {c with TYPES := c.TYPES ++ definitions (groupValue c.TYPES c.TYPES.length
    (Nat.le_refl _) sts h) sts.length}

def parentSyntax (p : Option Nat) : List heaptype :=
  p.toList.map (fun k => .VarHT (.StatX k))

/-- The exact source parent annotations selected by the earlier-parent skeleton.
No validity test or completed-signature comparison is part of this layout. -/
def ParentLayout (base : Nat) (sts : List SpecTec.subtype)
    (parents : List (Option Nat)) : Prop :=
  parents.length = sts.length ∧ ∀ i p, parents[i]? = some p →
    ∃ f st, sts[i]? = some (.SubT f (parentSyntax p) st) ∧
      ∀ k, p = some k → k < base+i

theorem mapP_get {α β : Type} (P : α → Prop) (f : (x : α) → P x → β)
    (xs : List α) (h : ∀ x ∈ xs, P x) (i : Nat) (x : α)
    (hx : xs[i]? = some x) (hp : P x) :
    (mapP P f xs h)[i]? = some (f x hp) := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons y ys ih =>
    cases i with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst x; rfl
    | succ i =>
      exact ih (fun z hz => h z (by simp [hz])) i (by simpa using hx)

theorem definition_lookup (table : List deftype) (rt : rectype) (width i : Nat)
    (hi : i < width) :
    (table ++ definitions rt width)[table.length+i]? = some (.DefT rt i) := by
  simp [definitions, List.getElem?_append_right (Nat.le_add_right _ _), hi]

theorem index_unroll (table : List deftype) (rt : rectype) (width : Nat)
    (i : Fin (table.length+width)) :
    ∃ dt, (table ++ definitions rt width)[i.val]? = some dt ∧
      unrollHeaptype (indexValue table table.length width (Nat.le_refl _) i) rt = .DefHT dt := by
  by_cases hi : i.val < table.length
  · refine ⟨table[i.val], ?_, ?_⟩
    · simp [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
    · simp [indexValue, Nat.not_le_of_gt hi, unrollHeaptype]
  · have hle : table.length ≤ i.val := by omega
    have hlocal : i.val-table.length < width := by omega
    refine ⟨.DefT rt (i.val-table.length), ?_, ?_⟩
    · rw [List.getElem?_append_right hle]
      simp [definitions, hlocal]
    · simp [indexValue, hle, unrollHeaptype, unrollTypevar]

theorem group_unroll (table : List deftype) (sts : List SpecTec.subtype)
    (h : GroupBound (table.length+sts.length) sts) (i : Nat)
    (f : final) (ps : List heaptype) (st : strtype)
    (hg : sts[i]? = some (.SubT f ps st))
    (hs : SubBound (table.length+sts.length) (.SubT f ps st)) :
    unrollDeftypeResult (.DefT (groupValue table table.length (Nat.le_refl _) sts h) i) =
      some (unrollSubtype (subValue table table.length sts.length (Nat.le_refl _)
        (.SubT f ps st) hs) (groupValue table table.length (Nat.le_refl _) sts h)) := by
  have hm := mapP_get _ (subValue table table.length sts.length (Nat.le_refl _))
    sts h i (.SubT f ps st) hg hs
  simp only [groupValue, unrollDeftypeResult, unrollRectype, unrollSubtypes,
    List.getElem?_map, hm, Option.map_some]

theorem edges (c : context) (sts : List SpecTec.subtype)
    (h : GroupBound (c.TYPES.length+sts.length) sts) (parents : List (Option Nat))
    (hp : ParentLayout c.TYPES.length sts parents) :
    ConstructiveNominalPlan.Edges (extended c sts h) c.TYPES.length parents := by
  intro i p hget
  obtain ⟨f, st, hsource, hbefore⟩ := hp.2 i p hget
  have hi : i < sts.length := by
    rw [← hp.1]
    exact (List.getElem?_eq_some_iff.mp hget).1
  have hs := h _ (List.mem_of_getElem? hsource)
  let rt := groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h
  let shape := unrollStrtype
    (strValue c.TYPES c.TYPES.length sts.length (Nat.le_refl _) st hs.2) rt
  refine ⟨.DefT rt i, f, shape, definition_lookup c.TYPES rt sts.length i hi, ?_⟩
  have hu := group_unroll c.TYPES sts h i f (parentSyntax p) st hsource hs
  cases p with
  | none =>
    simpa [subValue, parentSyntax, mapP, unrollSubtype, unrollHeaptypes, shape, rt] using hu
  | some k =>
    have hkbound : k < c.TYPES.length+sts.length := Nat.lt_trans (hbefore k rfl) (by omega)
    obtain ⟨dt,hdt,hunroll⟩ := index_unroll c.TYPES rt sts.length ⟨k,hkbound⟩
    refine ⟨hbefore k rfl, dt, hdt, ?_⟩
    simpa [subValue, parentSyntax, mapP, heapValue, unrollSubtype, unrollHeaptypes,
      hunroll, shape, rt] using hu

theorem ready (c : context) (sts : List SpecTec.subtype)
    (h : GroupBound (c.TYPES.length+sts.length) sts) (parents : List (Option Nat))
    (hp : ParentLayout c.TYPES.length sts parents) (hc : CandidateTypeReady.Ready c) :
    CandidateTypeReady.Ready (extended c sts h) := by
  let rt := groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h
  have hedges := edges c sts h parents hp
  apply CandidateTypeReadyExtension.ready_append c (definitions rt sts.length) hc
  · intro p dt hnew hlookup
    have hplen := (List.getElem?_eq_some_iff.mp hlookup).1
    have hi : p-c.TYPES.length < sts.length := by
      simp only [List.length_append, definitions, List.length_map, List.length_range] at hplen
      omega
    have hget : (c.TYPES ++ definitions rt sts.length)[p]? =
        some (.DefT rt (p-c.TYPES.length)) := by
      simp [definitions, List.getElem?_append_right hnew, hi]
    have heq := Option.some.inj (hlookup.symm.trans hget)
    subst dt
    exact ConstructiveTypeClosed.definition_fixed c.TYPES _ c.TYPES.length
      (Nat.le_refl _) sts h _
  · intro p hnew hpbound
    have hi : p-c.TYPES.length < parents.length := by
      simp only [List.length_append, definitions, List.length_map, List.length_range] at hpbound
      rw [hp.1]
      omega
    obtain ⟨dt,f,st,hget,hedge⟩ := hedges _ _ (List.getElem?_eq_getElem hi)
    have hpos : c.TYPES.length+(p-c.TYPES.length) = p := Nat.add_sub_cancel' hnew
    rw [hpos] at hget hedge
    cases hpar : parents[p-c.TYPES.length] with
    | none =>
      rw [hpar] at hedge
      exact ⟨dt,f,[],st,hget,hedge,by simp⟩
    | some k =>
      rw [hpar] at hedge
      obtain ⟨hk,target,htarget,hu⟩ := hedge
      refine ⟨dt,f,[.DefHT target],st,hget,hu,?_⟩
      intro j hj
      have hj0 : j = 0 := by simpa using hj
      subst j
      exact ⟨k,target,hk,htarget,rfl⟩

theorem planned_sound (c : context) (sts : List SpecTec.subtype)
    (h : GroupBound (c.TYPES.length+sts.length) sts) (parents : List (Option Nat))
    (hp : ParentLayout c.TYPES.length sts parents) (hc : CandidateTypeReady.Ready c)
    (p q : Nat) (hpb : p < (extended c sts h).TYPES.length)
    (hqb : q < (extended c sts h).TYPES.length) :
    ConstructiveNominalPlan.matchPlanned (ValidatedMatchIndexFuel.matchIndex c)
      c.TYPES.length parents p q = true →
    ValidatedMatchIndexFuel.matchIndex (extended c sts h) p q = true := by
  apply ConstructiveNominalPlan.matches_sound c (extended c sts h) _ parents rfl
    (ready c sts h parents hp hc) (edges c sts h parents hp)
  · simpa [definitions] using hp.1.symm
  · exact hpb
  · exact hqb

theorem planned_exact (c : context) (sts : List SpecTec.subtype)
    (h : GroupBound (c.TYPES.length+sts.length) sts) (parents : List (Option Nat))
    (hp : ParentLayout c.TYPES.length sts parents) (hc : CandidateTypeReady.Ready c)
    (hfresh : ∀ p i : Nat, c.TYPES[p]? ≠ some (deftype.DefT
      (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h) i))
    (p q : Nat) (hpb : p < (extended c sts h).TYPES.length)
    (hqb : q < (extended c sts h).TYPES.length) :
    ConstructiveNominalPlan.matchPlanned (ValidatedMatchIndexFuel.matchIndex c)
      c.TYPES.length parents p q =
    ValidatedMatchIndexFuel.matchIndex (extended c sts h) p q := by
  apply ConstructiveNominalPlan.planned_exact c (extended c sts h) _ parents rfl
    (ready c sts h parents hp hc) (edges c sts h parents hp)
  · simpa [definitions] using hp.1.symm
  · exact ConstructiveNominalPlan.fresh_no_aliases c (extended c sts h) _ _ rfl hfresh
  · exact hpb
  · exact hqb

end properties.wasm_module_ok.ConstructiveTypeEnvironment
