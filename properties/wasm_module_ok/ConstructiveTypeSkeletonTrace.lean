import properties.wasm_module_ok.ConstructiveTypeSkeleton
import properties.wasm_module_ok.RectypeSubMatchTrace
import properties.wasm_module_ok.RectypeStaticBound
import properties.wasm_module_ok.ValidatedStrtypeSubstitution
import properties.wasm_module_ok.UnrollPositionBridge
import properties.wasm_module_ok.MatchStrtypeConditional

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeSkeletonTrace
open SpecTec SpecTecExecution
open properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ConstructiveTypeSkeleton

def kind : strtype → Kind
  | .DefStructT _ => .structK
  | .DefArrayT _ => .arrayK
  | .DefFuncT _ => .funcK

def header : SpecTec.subtype → Header
  | .SubT f _ st => ⟨f, kind st⟩

/-- Proof-side connection to the stored type table. The generator maintains
headers alongside its constructed table and does not run this interpreter. -/
def headerAt (dts : List deftype) (i : Nat) : Option Header := do
  let dt ← dts[i]?
  let st ← unrollDeftypeResult dt
  pure (header st)

def Tracks (c : context) (hs : List Header) : Prop :=
  hs.length = c.TYPES.length ∧ ∀ i, hs[i]? = headerAt c.TYPES i

theorem match_kind (dts : List deftype) (a b : strtype) (start finish : Nat)
    (h : Eval specTecProgram (.call ⟨Bool, SpecTecCall.«$match_strtype» dts a b⟩)
      start (.success (.of true)) finish) : kind a = kind b := by
  by_contra hne
  have htag : MatchStrtypeConditional.strTag a ≠ MatchStrtypeConditional.strTag b := by
    cases a <;> cases b <;> simp_all [kind, MatchStrtypeConditional.strTag]
  have hfalse := MatchStrtypeConditional.mixed_pair_false dts a b start htag
  have hdet : PrimitiveDeterministic specTecProgram := by
    intro request x y hp
    cases hp
  have heq := (eval_deterministic hdet h hfalse).1
  cases heq

theorem kind_roll (st : strtype) (lo hi : Nat) :
    kind (rollStrtype st lo hi) = kind st := by
  cases st <;> rfl

theorem kind_unroll (st : strtype) (rt : rectype) :
    kind (unrollStrtype st rt) = kind st := by
  cases st <;> rfl

theorem kind_subst (st out : strtype) (dts : List deftype)
    (h : substStrtypeResult st dts = some out) : kind out = kind st := by
  cases st <;> simp only [substStrtypeResult, Option.map_eq_some_iff] at h <;>
    obtain ⟨x, _, rfl⟩ := h <;> rfl

theorem headerAt_new (before after : context) (sts : List SpecTec.subtype)
    (start finish i : Nat) (s : SpecTec.subtype)
    (hrect : Eval specTecProgram
      (.call ⟨context, SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hsource : sts[i]? = some s) :
    headerAt after.TYPES (before.TYPES.length + i) = some (header s) := by
  have hi := (List.getElem?_eq_some_iff.mp hsource).1
  obtain ⟨dts, hafter, hpos⟩ :=
    RectypeAppendedShape.rectype_ok_appended_position_shape
      before after sts start finish hrect
  obtain ⟨rt, hdt, htrans⟩ := hpos i hi
  cases rt with
  | RecT out =>
    cases s with
    | SubT f ps st =>
      obtain ⟨ps', st', hout, hsubst⟩ :=
        ValidatedStrtypeSubstitution.rectype_ok_appended_strtype_subst
          before after sts out start finish i dts f ps st hrect hi hsource hafter hdt
      have hk : kind st' = kind st :=
        (kind_subst _ _ _ hsubst).trans (kind_roll st _ _)
      simp [headerAt, hafter, List.getElem?_append_right
        (show before.TYPES.length ≤ before.TYPES.length + i by omega),
        Nat.add_sub_cancel_left, hdt, Option.bind_some,
        UnrollPositionBridge.unroll_deftype_at out i f ps' st' hout,
        header, kind_unroll, hk]

theorem tracks_extend (before after : context) (hs : List Header)
    (sts : List SpecTec.subtype) (start finish : Nat)
    (htrack : Tracks before hs)
    (hrect : Eval specTecProgram
      (.call ⟨context, SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish) :
    Tracks after (hs ++ sts.map header) := by
  have htracklen := htrack.1
  obtain ⟨dts, hafter, hlen⟩ :=
    RectypeLengthValidation.rectype_ok_appended_types_length
      before after sts start finish hrect
  constructor
  · simp [hafter, htrack.1, hlen]
  · intro i
    by_cases hi : i < hs.length
    · rw [List.getElem?_append_left hi, htrack.2 i]
      simp only [headerAt, hafter,
        List.getElem?_append_left (htrack.1 ▸ hi)]
    · by_cases hj : i - hs.length < sts.length
      · have hget := List.getElem?_eq_getElem hj
        have hnew := headerAt_new before after sts start finish
          (i - hs.length) sts[i - hs.length] hrect hget
        have hind : before.TYPES.length + (i - hs.length) = i := by omega
        rw [hind] at hnew
        rw [hnew, List.getElem?_append_right (by omega)]
        simp only [List.getElem?_map, hget, Option.map_some]
      · have hfull : (hs ++ sts.map header).length ≤ i := by
          simp only [List.length_append, List.length_map]
          omega
        have htypes : after.TYPES.length ≤ i := by simp only [hafter, List.length_append, hlen]; omega
        simp [List.getElem?_eq_none hfull, headerAt, List.getElem?_eq_none htypes]

/-- Original subtype matching forces precisely an earlier, non-final parent
of the same structural kind. No readiness or full-module hypothesis is used. -/
theorem original_parent (c : context) (x y : Nat) (st : strtype)
    (start finish : Nat)
    (h : Eval specTecProgram
      (.call ⟨Unit, SpecTecCall.Subtype_sub_ok' c x st (.VarHT (.StatX y))⟩)
      start (.success (.of ())) finish) :
    y < x ∧ headerAt c.TYPES y = some ⟨.NoFinal, kind st⟩ := by
  obtain ⟨dt, f, ps, target, middle, hlookup, hunroll, hmatch, hlt, hfin⟩ :=
    SubtypeStaticMatchTrace.subtype_sub_ok_static_match_trace c x y st start finish h
  have hu := (UnrollInterface.unrolldt_success_iff dt (.SubT f ps target)
    start middle).1 hunroll |>.1
  have hk := match_kind c.TYPES st target middle finish hmatch
  exact ⟨hlt, by simp [headerAt, hlookup, hu, header, hfin, hk]⟩

theorem tracks_exist (c : context) (hc : ValidatedTypeChain.ValidatedTypes c) :
    ∃ hs, Tracks c hs := by
  induction hc with
  | seed c hnil => exact ⟨[], by simp [Tracks, headerAt, hnil]⟩
  | append before after sts start finish hbefore hrect ih =>
    obtain ⟨hs, htrack⟩ := ih
    exact ⟨hs ++ sts.map header, tracks_extend before after hs sts start finish htrack hrect⟩

def supers : SpecTec.subtype → List heaptype
  | .SubT _ ps _ => ps

/-- This projection is used only in the backward coverage theorem. The theorem
below proves that the original successful source has exactly this parent list. -/
def parentOf : List heaptype → Option Nat
  | [.VarHT (.StatX i)] => some i
  | _ => none

def entryOf (st : SpecTec.subtype) : Entry := ⟨header st, parentOf (supers st)⟩

theorem original_entry (before after : context) (hs : List Header)
    (sts : List SpecTec.subtype) (start finish i : Nat) (s : SpecTec.subtype)
    (htrack : Tracks before hs)
    (hrect : Eval specTecProgram
      (.call ⟨context, SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hsource : sts[i]? = some s) :
    EntryAllowed (hs ++ (sts.take i).map header) (entryOf s) ∧
      supers s = (entryOf s).parent.toList.map (fun y => .VarHT (.StatX y)) := by
  have hi := (List.getElem?_eq_some_iff.mp hsource).1
  have htracklen := htrack.1
  have haftertrack := tracks_extend before after hs sts start finish htrack hrect
  obtain ⟨dts, hafter, a, b, hiter⟩ :=
    RectypeSourceValidation.rectype_ok_extract_validation_iter
      before after sts start finish hrect
  have hmem : s ∈ sts := List.mem_iff_getElem?.2 ⟨i, hsource⟩
  obtain ⟨sa, sb, hsub⟩ :=
    RectypeSourceValidation.validation_iter_member _ sts a b hiter s hmem
  cases s with
  | SubT f ps st =>
    have hlen := (SubtypeValidation.subtype_success_iff_calls _ f ps st sa sb).1 hsub |>.1
    cases ps with
    | nil => simp [EntryAllowed, entryOf, supers, parentOf]
    | cons ht rest =>
      have hrest : rest = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at hlen
        omega
      subst rest
      obtain ⟨n, y, ca, cb, hshape, hcall⟩ :=
        RectypeSubMatchTrace.rectype_ok_supertype_static_call
          before after sts start finish i f [ht] st ht hrect hi hsource (by simp)
      subst ht
      have hp := (original_parent after (before.TYPES.length+n) y st ca cb hcall).2
      have hy := RectypeStaticBound.rectype_ok_source_static_lt
        before after sts start finish i 0 y f [.VarHT (.StatX y)] st
          hrect hi hsource (by rfl)
      have hget : (hs ++ sts.map header)[y]? = some ⟨.NoFinal, kind st⟩ :=
        (haftertrack.2 y).trans hp
      have hpre : (hs ++ (sts.take i).map header)[y]? =
          (hs ++ sts.map header)[y]? := by
        by_cases hshort : y < hs.length
        · rw [List.getElem?_append_left hshort, List.getElem?_append_left hshort]
        · rw [List.getElem?_append_right (Nat.le_of_not_gt hshort),
            List.getElem?_append_right (Nat.le_of_not_gt hshort)]
          have hshort' : hs.length ≤ y := Nat.le_of_not_gt hshort
          have hy' : y < hs.length + i := by simpa only [htracklen] using hy
          have hshift : y - hs.length < i := Nat.sub_lt_left_of_lt_add hshort' hy'
          simp only [List.getElem?_map,
            List.getElem?_take_of_lt hshift]
      constructor
      · exact ⟨⟨.NoFinal, kind st⟩, hpre.trans hget, rfl, rfl⟩
      · rfl

theorem allowed_positions (hs : List Header) (es : List Entry) :
    Allowed hs es ↔ ∀ i e, es[i]? = some e →
      EntryAllowed (hs ++ (es.take i).map Entry.header) e := by
  induction es generalizing hs with
  | nil => simp [Allowed]
  | cons e es ih =>
    constructor
    · rintro ⟨hhead, htail⟩ i v hget
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
        subst v
        simpa using hhead
      | succ j =>
        have h := (ih (hs ++ [e.header])).1 htail j v hget
        simpa [List.take_succ_cons, List.append_assoc] using h
    · intro h
      refine ⟨?_, (ih (hs ++ [e.header])).2 ?_⟩
      · simpa using h 0 e rfl
      · intro i v hget
        have hnext := h (i+1) v hget
        simpa [List.take_succ_cons, List.append_assoc] using hnext

/-- Every original successful group has a supported skeleton, and extracting
it loses no parent annotation. This is backward coverage of the skeleton only;
constructing every compatible field/signature remains a separate obligation. -/
theorem original_skeleton (before after : context) (hs : List Header)
    (sts : List SpecTec.subtype) (start finish : Nat)
    (htrack : Tracks before hs)
    (hrect : Eval specTecProgram
      (.call ⟨context, SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish) :
    Gen.support (skeleton hs) (sts.map entryOf) ∧
      ∀ s ∈ sts, supers s = (entryOf s).parent.toList.map (fun y => .VarHT (.StatX y)) := by
  constructor
  · rw [skeleton_support, allowed_positions]
    intro i e hget
    rw [List.getElem?_map, Option.map_eq_some_iff] at hget
    obtain ⟨s, hsget, rfl⟩ := hget
    have h := (original_entry before after hs sts start finish i s htrack hrect hsget).1
    simpa [← List.map_take, List.map_map, entryOf, Function.comp_def] using h
  · intro s hmem
    obtain ⟨i, hget⟩ := List.mem_iff_getElem?.1 hmem
    exact (original_entry before after hs sts start finish i s htrack hrect hget).2

end properties.wasm_module_ok.ConstructiveTypeSkeletonTrace
