import properties.wasm_module_ok.ConstructiveHeapPlan

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeMetadata
open SpecTec properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open ConstructiveTypeSkeleton ConstructiveTypeSkeletonTrace
open ConstructiveTypeCopy ConstructiveTypeCopySemantics ConstructiveTypeEnvironment

def kindAt (headers : List Header) (p : Nat) : Kind :=
  ((headers[p]?).map Header.kind).getD .structK

theorem kind_value (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : strtype) (h : StrBound (base+width) st) :
    kind (strValue table base width hle st h) = kind st := by
  cases st with
  | DefStructT s => cases s; rfl
  | DefArrayT a => cases a; rfl
  | DefFuncT f => cases f; rfl

theorem header_new (c : context) (sts : List SpecTec.subtype)
    (h : GroupBound (c.TYPES.length+sts.length) sts) (i : Nat) (s : SpecTec.subtype)
    (hget : sts[i]? = some s) :
    headerAt (extended c sts h).TYPES (c.TYPES.length+i) = some (header s) := by
  rcases s with ⟨f,ps,st⟩
  have hs := h _ (List.mem_of_getElem? hget)
  have hi := (List.getElem?_eq_some_iff.mp hget).1
  let rt := groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h
  have hlookup : (extended c sts h).TYPES[c.TYPES.length+i]? = some (.DefT rt i) :=
    definition_lookup c.TYPES rt sts.length i hi
  have hu := group_unroll c.TYPES sts h i f ps st hget hs
  simp [headerAt, hlookup, rt, hu, subValue, unrollSubtype, header, kind_unroll, kind_value]

/-- Metadata remains exact immediately after structural closure, before the
new group's subtype compatibility has been proved. -/
theorem tracks_closed (c : context) (hs : List Header)
    (sts : List SpecTec.subtype) (h : GroupBound (c.TYPES.length+sts.length) sts)
    (ht : Tracks c hs) : Tracks (extended c sts h) (hs ++ sts.map header) := by
  have htracklen := ht.1
  have hlen : (extended c sts h).TYPES.length = c.TYPES.length+sts.length := by
    simp [extended, definitions]
  constructor
  · simp [hlen, ht.1]
  · intro i
    by_cases hi : i < hs.length
    · rw [List.getElem?_append_left hi, ht.2 i]
      simp only [headerAt, extended, List.getElem?_append_left (ht.1 ▸ hi)]
    · by_cases hj : i-hs.length < sts.length
      · have hget := List.getElem?_eq_getElem hj
        have hnew := header_new c sts h (i-hs.length) sts[i-hs.length] hget
        have hpos : c.TYPES.length+(i-hs.length) = i := by omega
        rw [hpos] at hnew
        rw [hnew, List.getElem?_append_right (by omega)]
        simp only [List.getElem?_map, hget, Option.map_some]
      · have htotal : (hs ++ sts.map header).length ≤ i := by
          simp only [List.length_append, List.length_map]
          omega
        have htypes : (extended c sts h).TYPES.length ≤ i := by omega
        simp [List.getElem?_eq_none htotal, headerAt, List.getElem?_eq_none htypes]

theorem tracks_kinds (c : context) (hs : List Header)
    (ht : Tracks c hs) (hr : CandidateTypeReady.Ready c) :
    ConstructiveHeapPlan.TracksKinds c (kindAt hs) := by
  intro p dt hp
  obtain ⟨dt',f,ps,st,hget,hu,_⟩ := hr.unrolledPredecessors p
    (List.getElem?_eq_some_iff.mp hp).1
  have heq : dt' = dt := Option.some.inj (hget.symm.trans hp)
  subst dt'
  have hmeta : hs[p]? = some (header (.SubT f ps st)) := by
    rw [ht.2 p]
    simp [headerAt, hp, hu]
  exact ⟨f,ps,st,hu,by simp [kindAt,hmeta,header]⟩

theorem heap_sound (c : context) (hs : List Header) (sts : List SpecTec.subtype)
    (h : GroupBound (c.TYPES.length+sts.length) sts) (parents : List (Option Nat))
    (hp : ParentLayout c.TYPES.length sts parents) (hc : CandidateTypeReady.Ready c)
    (ht : Tracks c hs) (metadata : List Header) (hm : metadata = hs ++ sts.map header)
    (a b : heaptype) (ha : HeapBound (extended c sts h).TYPES.length a)
    (hb : HeapBound (extended c sts h).TYPES.length b) :
    ConstructiveHeapPlan.heap (kindAt metadata)
      (ConstructiveNominalPlan.matchPlanned (ValidatedMatchIndexFuel.matchIndex c)
        c.TYPES.length parents) a b = true →
    (ReadyHeapMatch.readyHeapMatch (extended c sts h) a b).getD false = true := by
  subst metadata
  exact ConstructiveHeapPlan.heap_sound (extended c sts h) _ _
    (tracks_kinds _ _ (tracks_closed c hs sts h ht) (ready c sts h parents hp hc))
    (fun p q hpb hqb => planned_sound c sts h parents hp hc p q hpb hqb) a b ha hb

theorem heap_exact (c : context) (hs : List Header) (sts : List SpecTec.subtype)
    (h : GroupBound (c.TYPES.length+sts.length) sts) (parents : List (Option Nat))
    (hp : ParentLayout c.TYPES.length sts parents) (hc : CandidateTypeReady.Ready c)
    (ht : Tracks c hs) (metadata : List Header) (hm : metadata = hs ++ sts.map header)
    (hfresh : ∀ p i : Nat, c.TYPES[p]? ≠ some (deftype.DefT
      (groupValue c.TYPES c.TYPES.length (Nat.le_refl _) sts h) i))
    (a b : heaptype) (ha : HeapBound (extended c sts h).TYPES.length a)
    (hb : HeapBound (extended c sts h).TYPES.length b) :
    ConstructiveHeapPlan.heap (kindAt metadata)
      (ConstructiveNominalPlan.matchPlanned (ValidatedMatchIndexFuel.matchIndex c)
        c.TYPES.length parents) a b =
    (ReadyHeapMatch.readyHeapMatch (extended c sts h) a b).getD false := by
  subst metadata
  exact ConstructiveHeapPlan.heap_exact (extended c sts h) _ _
    (tracks_kinds _ _ (tracks_closed c hs sts h ht) (ready c sts h parents hp hc))
    (fun p q hpb hqb => planned_exact c sts h parents hp hc hfresh p q hpb hqb) a b ha hb

end properties.wasm_module_ok.ConstructiveTypeMetadata
