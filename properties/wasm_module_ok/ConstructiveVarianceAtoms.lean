import properties.wasm_module_ok.ConstructiveHeapPlan
import properties.wasm_module_ok.MatchFieldConditional
import properties.wasm_module_ok.ConstructiveTypeShapes

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveVarianceAtoms
open SpecTec properties.wasm_module_ok
open ConstructiveTypeCopy ConstructiveTypeAtoms

inductive Direction where
  | below | above | same
  deriving DecidableEq, Repr

def directed {α : Type} (d : Direction) (r : α → α → Bool) (a b : α) : Bool :=
  match d with
  | .below => r a b
  | .above => r b a
  | .same => r a b && r b a

def heapDomain (bound : Nat) : List heaptype :=
  HeaptypeValidation.baseHeaptypes ++
    (List.range bound).map (fun i => .VarHT (.StatX i))

theorem heap_domain (bound : Nat) (h : heaptype) :
    h ∈ heapDomain bound ↔ HeapBound bound h := by
  cases h <;> simp [heapDomain, HeapBound, HeaptypeValidation.baseHeaptypes]
  case VarHT tv => cases tv <;> simp

/-- Build the finite type-directed choice table before drawing a value. This
examines only atomic references and the planned kind/parent relation; no
signature, recursive group, or sampled candidate is validated or rejected. -/
def relatedHeaps (d : Direction) (r : heaptype → heaptype → Bool) (target : heaptype) :
    List heaptype → List heaptype
  | [] => []
  | h::hs =>
    if directed d r h target then h::relatedHeaps d r target hs
    else relatedHeaps d r target hs

theorem related_heaps (d : Direction) (r : heaptype → heaptype → Bool)
    (target out : heaptype) (xs : List heaptype) :
    out ∈ relatedHeaps d r target xs ↔ out ∈ xs ∧ directed d r out target = true := by
  induction xs with
  | nil => simp [relatedHeaps]
  | cons h hs ih =>
    by_cases hh : directed d r h target = true
    · by_cases ho : out = h
      · subst out; simp [relatedHeaps, hh]
      · simp [relatedHeaps, hh, ih, ho]
    · by_cases ho : out = h
      · subst out; simp [relatedHeaps, hh, ih]
      · simp [relatedHeaps, hh, ih, ho]

/-- The inherited target is a known legal choice, so this table is nonempty
by construction. It is never a replacement for a failed sampled candidate. -/
def heaps (bound : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (target : heaptype) : Gen heaptype :=
  choose target (relatedHeaps d r target (heapDomain bound))

theorem heaps_support (bound : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (target : heaptype) (ht : HeapBound bound target) (hr : r target target = true)
    (out : heaptype) : Gen.support (heaps bound d r target) out ↔
      HeapBound bound out ∧ directed d r out target = true := by
  simp only [heaps, support_choose, List.mem_cons, related_heaps, heap_domain]
  have hd : directed d r target target = true := by cases d <;> simp [directed, hr]
  constructor
  · rintro (rfl | h)
    · exact ⟨ht,hd⟩
    · exact h
  · exact Or.inr

def nulls (d : Direction) (target : null) : Gen null :=
  match d, target with
  | .below, .Null => choose .Null [.NoNull]
  | .above, .NoNull => choose .NoNull [.Null]
  | _, n => pure n

theorem nulls_support (d : Direction) (target out : null) :
    Gen.support (nulls d target) out ↔
      directed d MatchNullValidation.matchNullResult out target = true := by
  cases d <;> cases target <;> cases out <;>
    simp [nulls, directed, MatchNullValidation.matchNullResult]

def refs (bound : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (target : reftype) : Gen reftype :=
  match target with
  | .«% %» nu ht => do
    let n ← nulls d nu
    let h ← heaps bound d r ht
    pure (.«% %» n h)

theorem refs_support (bound : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, HeapBound bound h → r h h = true)
    (target : reftype) (ht : RefBound bound target) (out : reftype) :
    Gen.support (refs bound d r target) out ↔ RefBound bound out ∧
      directed d (MatchReftypeConditional.matchReftypeResult r) out target = true := by
  rcases target with ⟨nu,h⟩
  rcases out with ⟨nu',h'⟩
  simp only [refs, Gen.Support.support_bind, Gen.Support.support_pure,
    reftype.«% %».injEq, exists_eq_right, heaps_support bound d r h ht (hr h ht),
    nulls_support]
  cases d <;> simp [directed, MatchReftypeConditional.matchReftypeResult,
    RefBound, and_assoc, and_left_comm, and_comm]

def ValidVal (bound : Nat) : valtype → Prop
  | .BotT => False
  | .RefT r => RefBound bound r
  | _ => True

def vals (bound : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (target : valtype) (ht : ValidVal bound target) : Gen valtype :=
  match target with
  | .NumT n => pure (.NumT n)
  | .VecT v => pure (.VecT v)
  | .RefT t => valtype.RefT <$> refs bound d r t
  | .BotT => False.elim ht

theorem vals_support (bound : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, HeapBound bound h → r h h = true)
    (target : valtype) (ht : ValidVal bound target) (out : valtype) :
    Gen.support (vals bound d r target ht) out ↔ ValidVal bound out ∧
      directed d (MatchValtypeConditional.matchValtypeResult r) out target = true := by
  cases target with
  | BotT => exact False.elim ht
  | NumT n => cases out <;> cases d <;>
      simp [vals, ValidVal, directed, MatchValtypeConditional.matchValtypeResult, eq_comm]
  | VecT v => cases out <;> cases d <;>
      simp [vals, ValidVal, directed, MatchValtypeConditional.matchValtypeResult, eq_comm]
  | RefT t =>
    cases out with
    | RefT o =>
      have hexact := refs_support bound d r hr t ht o
      cases d <;> simpa [vals, ValidVal, directed,
        MatchValtypeConditional.matchValtypeResult] using hexact
    | NumT n => cases d <;> simp [vals, ValidVal, directed, MatchValtypeConditional.matchValtypeResult]
    | VecT v => cases d <;> simp [vals, ValidVal, directed, MatchValtypeConditional.matchValtypeResult]
    | BotT => simp [vals, ValidVal]

def ValidStorage (bound : Nat) : storagetype → Prop
  | .ValStorageT v => ValidVal bound v
  | .PackStorageT p => p = .I8 ∨ p = .I16

def storage (bound : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (target : storagetype) (ht : ValidStorage bound target) : Gen storagetype :=
  match target with
  | .ValStorageT v => storagetype.ValStorageT <$> vals bound d r v ht
  | .PackStorageT p => pure (.PackStorageT p)

theorem storage_support (bound : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, HeapBound bound h → r h h = true)
    (target : storagetype) (ht : ValidStorage bound target) (out : storagetype) :
    Gen.support (storage bound d r target ht) out ↔ ValidStorage bound out ∧
      directed d (MatchStorageConditional.storageMatch r) out target = true := by
  cases target with
  | ValStorageT v =>
    cases out with
    | ValStorageT o =>
      have hexact := vals_support bound d r hr v ht o
      cases d <;> simpa [storage, ValidStorage, directed,
        MatchStorageConditional.storageMatch] using hexact
    | PackStorageT p => cases d <;> simp [storage, directed, MatchStorageConditional.storageMatch]
  | PackStorageT p =>
    cases out with
    | ValStorageT v => cases d <;> simp [storage, directed, MatchStorageConditional.storageMatch]
    | PackStorageT q =>
      cases d <;> simp [storage, directed, MatchStorageConditional.storageMatch, ValidStorage,
        eq_comm] <;> intro he <;> cases he <;> exact ht

def ValidField (bound : Nat) : fieldtype → Prop
  | .FieldT _ s => ValidStorage bound s

def fields (bound : Nat) (r : heaptype → heaptype → Bool)
    (target : fieldtype) (ht : ValidField bound target) : Gen fieldtype :=
  match target with
  | .FieldT .Cons s => fieldtype.FieldT .Cons <$> storage bound .below r s ht
  | .FieldT .Var s => fieldtype.FieldT .Var <$> storage bound .same r s ht

theorem fields_support (bound : Nat) (r : heaptype → heaptype → Bool)
    (hr : ∀ h, HeapBound bound h → r h h = true)
    (target : fieldtype) (ht : ValidField bound target) (out : fieldtype) :
    Gen.support (fields bound r target ht) out ↔ ValidField bound out ∧
      MatchFieldConditional.fieldMatch r out target = true := by
  rcases target with ⟨mu,s⟩
  rcases out with ⟨nu,t⟩
  cases mu <;> cases nu <;>
    simp [fields, ValidField, storage_support bound _ r hr s ht,
      MatchFieldConditional.fieldMatch, directed]

theorem heaps_finite (b : Nat) (d : Direction) (r : heaptype → heaptype → Bool) (t : heaptype) :
    FiniteConstruction (heaps b d r t) := finite_choose _ _

theorem nulls_finite (d : Direction) (t : null) : FiniteConstruction (nulls d t) := by
  cases d <;> cases t <;> simp only [nulls]
  all_goals first | exact finite_choose _ _ | trivial

theorem refs_finite (b : Nat) (d : Direction) (r : heaptype → heaptype → Bool) (t : reftype) :
    FiniteConstruction (refs b d r t) := by
  cases t
  exact ⟨nulls_finite _ _, fun _ => ⟨heaps_finite _ _ _ _, fun _ => trivial⟩⟩

theorem vals_finite (b : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (t : valtype) (ht : ValidVal b t) : FiniteConstruction (vals b d r t ht) := by
  cases t with
  | NumT n => trivial
  | VecT v => trivial
  | RefT t => exact ⟨refs_finite b d r t, fun _ => trivial⟩
  | BotT => exact False.elim ht

theorem storage_finite (b : Nat) (d : Direction) (r : heaptype → heaptype → Bool)
    (t : storagetype) (ht : ValidStorage b t) : FiniteConstruction (storage b d r t ht) := by
  cases t with
  | ValStorageT v => exact ⟨vals_finite b d r v ht, fun _ => trivial⟩
  | PackStorageT p => trivial

theorem fields_finite (b : Nat) (r : heaptype → heaptype → Bool)
    (t : fieldtype) (ht : ValidField b t) : FiniteConstruction (fields b r t ht) := by
  rcases t with ⟨mu,s⟩
  cases mu <;> exact ⟨storage_finite b _ r s ht, fun _ => trivial⟩

theorem heap_bound_iff (c : context) (h : heaptype) :
    HeapBound c.TYPES.length h ↔ HeaptypeValidation.heaptypeValid c h = true := by
  cases h <;> simp [HeapBound, HeaptypeValidation.heaptypeValid]
  case VarHT t => cases t <;> simp [HeapBound, HeaptypeValidation.heaptypeValid]

theorem valid_val_iff (c : context) (v : valtype) :
    ValidVal c.TYPES.length v ↔ ValtypeValidation.valtypeValid c v = true := by
  cases v <;> simp [ValidVal, ValtypeValidation.valtypeValid]
  case RefT t => cases t; exact heap_bound_iff c _

theorem valid_storage_iff (c : context) (s : storagetype) :
    ValidStorage c.TYPES.length s ↔ StoragetypeValidation.storagetypeValid c s = true := by
  cases s <;> simp [ValidStorage, StoragetypeValidation.storagetypeValid, valid_val_iff]

theorem valid_field_iff (c : context) (f : fieldtype) :
    ValidField c.TYPES.length f ↔ FieldtypeValidation.fieldtypeValid c f = true := by
  cases f; exact valid_storage_iff c _

end properties.wasm_module_ok.ConstructiveVarianceAtoms
