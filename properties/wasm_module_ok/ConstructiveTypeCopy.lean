import properties.wasm_module_ok.ConstructiveRelocateIndices
import properties.wasm_module_ok.CandidateRectypeTable
import Mathlib.Data.List.Forall2
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopy
open SpecTec
open properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open properties.wasm_module_ok.ConstructiveRelocateIndices

/-- Source-shape invariant: all variable leaves are static and in the finite
source bound. It is established during construction, never tested on candidates. -/
def HeapBound (bound : Nat) : heaptype → Prop
  | .VarHT (.StatX i) => i < bound
  | .VarHT (.RecX _) | .DefHT _ => False
  | _ => True

def RefBound (b : Nat) : reftype → Prop
  | .«% %» _ h => HeapBound b h

def ValBound (b : Nat) : valtype → Prop
  | .RefT r => RefBound b r
  | _ => True

def StorageBound (b : Nat) : storagetype → Prop
  | .ValStorageT v => ValBound b v
  | .PackStorageT _ => True

def FieldBound (b : Nat) : fieldtype → Prop
  | .FieldT _ s => StorageBound b s

def StrBound (b : Nat) : strtype → Prop
  | .DefStructT (.StructT fs) => ∀ f ∈ fs, FieldBound b f
  | .DefArrayT (.ArrayT f) => FieldBound b f
  | .DefFuncT (.FuncT ins outs) => (∀ t ∈ ins, ValBound b t) ∧ (∀ t ∈ outs, ValBound b t)

def SubBound (b : Nat) : SpecTec.subtype → Prop
  | .SubT _ hs st => (∀ h ∈ hs, HeapBound b h) ∧ StrBound b st

def GroupBound (b : Nat) (sts : List SpecTec.subtype) : Prop := ∀ s ∈ sts, SubBound b s

/-- Traverse a finite structure with its already-established source invariant.
No sampled value is tested, discarded, or replaced. -/
def each {α β : Type} (P : α → Prop) (f : (x : α) → P x → Gen β) :
    (xs : List α) → (∀ x ∈ xs, P x) → Gen (List β)
  | [], _ => pure []
  | x :: xs, h => do
      let y ← f x (h x (by simp))
      let ys ← each P f xs (fun x hx => h x (by simp [hx]))
      pure (y :: ys)

theorem each_support {α β : Type} (P : α → Prop) (f : (x : α) → P x → Gen β)
    (xs : List α) (h : ∀ x ∈ xs, P x) (ys : List β) :
    Gen.support (each P f xs h) ys ↔
      List.Forall₂ (fun x y => ∃ hp, Gen.support (f x hp) y) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [each]
  | cons x xs ih =>
    constructor
    · intro hg
      simp only [each, Gen.Support.support_bind, Gen.Support.support_pure] at hg
      obtain ⟨y, hy, tail, ht, rfl⟩ := hg
      exact .cons ⟨h x (by simp), hy⟩ ((ih _ tail).1 ht)
    · intro hf
      cases hf with
      | cons hhead htail =>
        obtain ⟨hp, hg⟩ := hhead
        simp only [each, Gen.Support.support_bind, Gen.Support.support_pure]
        exact ⟨_, hg, _, (ih _ _).2 htail, rfl⟩

theorem each_finite {α β : Type} (P : α → Prop) (f : (x : α) → P x → Gen β)
    (hf : ∀ x hx, ConstructiveTypeAtoms.FiniteConstruction (f x hx))
    (xs : List α) (h : ∀ x ∈ xs, P x) :
    ConstructiveTypeAtoms.FiniteConstruction (each P f xs h) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨hf _ _, fun _ => ⟨ih _, fun _ => trivial⟩⟩

def heap (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ht : heaptype) (h : HeapBound (base+width) ht) : Gen heaptype :=
  match ht with
  | .VarHT (.StatX i) =>
      (fun j => heaptype.VarHT (.StatX j)) <$> relocate table base width hle ⟨i, h⟩
  | .VarHT (.RecX _) | .DefHT _ => False.elim h
  | other => pure other

def ref (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (rt : reftype) (h : RefBound (base+width) rt) : Gen reftype :=
  match rt with
  | .«% %» nu ht => (reftype.«% %» nu) <$> heap table base width hle ht h

def val (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (vt : valtype) (h : ValBound (base+width) vt) : Gen valtype :=
  match vt with
  | .RefT rt => valtype.RefT <$> ref table base width hle rt h
  | other => pure other

def storage (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : storagetype) (h : StorageBound (base+width) st) : Gen storagetype :=
  match st with
  | .ValStorageT v => storagetype.ValStorageT <$> val table base width hle v h
  | .PackStorageT p => pure (.PackStorageT p)

def field (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ft : fieldtype) (h : FieldBound (base+width) ft) : Gen fieldtype :=
  match ft with
  | .FieldT mu st => (fieldtype.FieldT mu) <$> storage table base width hle st h

def str (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : strtype) (h : StrBound (base+width) st) : Gen strtype :=
  match st with
  | .DefStructT (.StructT fs) =>
      (fun fs' => strtype.DefStructT (.StructT fs')) <$>
        each (FieldBound (base+width)) (field table base width hle) fs h
  | .DefArrayT (.ArrayT f) =>
      (fun f' => strtype.DefArrayT (.ArrayT f')) <$> field table base width hle f h
  | .DefFuncT (.FuncT ins outs) => do
      let ins' ← each (ValBound (base+width)) (val table base width hle) ins h.1
      let outs' ← each (ValBound (base+width)) (val table base width hle) outs h.2
      pure (.DefFuncT (.FuncT ins' outs'))

def sub (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : SpecTec.subtype) (h : SubBound (base+width) st) : Gen SpecTec.subtype :=
  match st with
  | .SubT fin hs st => do
      let hs' ← each (HeapBound (base+width)) (heap table base width hle) hs h.1
      let st' ← str table base width hle st h.2
      pure (.SubT fin hs' st')

/-- Whole-group inverse reification. Source group size and every source
constructor are retained, with all external static-index aliases available. -/
def group (table : List deftype) (base : Nat) (hle : base ≤ table.length)
    (sts : List SpecTec.subtype) (h : GroupBound (base+sts.length) sts) : Gen rectype :=
  rectype.RecT <$> each (SubBound (base+sts.length)) (sub table base sts.length hle) sts h

def Base (ht : heaptype) : Prop :=
  match ht with | .VarHT _ | .DefHT _ => False | _ => True

theorem raw_cases (bound : Nat) (ht : heaptype) (h : HeapBound bound ht) :
    Base ht ∨ ∃ i, ht = .VarHT (.StatX i) ∧ i < bound := by
  cases ht <;> try exact Or.inl trivial
  case DefHT dt => exact h.elim
  case VarHT tv =>
    cases tv with
    | StatX i => exact Or.inr ⟨i,rfl,h⟩
    | RecX i => exact h.elim

theorem base_bound (bound : Nat) (ht : heaptype) (h : Base ht) : HeapBound bound ht := by
  cases ht <;> try exact h
  exact h.elim

theorem heap_base (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ht : heaptype) (h : HeapBound (base+width) ht) (hb : Base ht) :
    heap table base width hle ht h = pure ht := by
  cases ht <;> simp_all [Base, heap]

theorem closed_heap_base (table : List deftype) (base width : Nat)
    (ht : heaptype) (h : Base ht) :
    substHeaptypeResult (rollHeaptype ht base (base+width)) table = some ht := by
  cases ht <;> simp_all [Base, rollHeaptype, substHeaptypeResult]

theorem heap_finite (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ht : heaptype) (h : HeapBound (base+width) ht) :
    ConstructiveTypeAtoms.FiniteConstruction (heap table base width hle ht h) := by
  rcases raw_cases (base+width) ht h with hb | ⟨i,rfl,hi⟩
  · rw [heap_base table base width hle ht h hb]
    trivial
  · exact ⟨relocate_finite _ _ _ _ _, fun _ => trivial⟩

theorem ref_finite (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (rt : reftype) (h : RefBound (base+width) rt) :
    ConstructiveTypeAtoms.FiniteConstruction (ref table base width hle rt h) := by
  cases rt
  exact ⟨heap_finite _ _ _ _ _ _, fun _ => trivial⟩

theorem val_finite (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (vt : valtype) (h : ValBound (base+width) vt) :
    ConstructiveTypeAtoms.FiniteConstruction (val table base width hle vt h) := by
  cases vt <;> try trivial
  exact ⟨ref_finite _ _ _ _ _ _, fun _ => trivial⟩

theorem storage_finite (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : storagetype) (h : StorageBound (base+width) st) :
    ConstructiveTypeAtoms.FiniteConstruction (storage table base width hle st h) := by
  cases st <;> try trivial
  exact ⟨val_finite _ _ _ _ _ _, fun _ => trivial⟩

theorem field_finite (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ft : fieldtype) (h : FieldBound (base+width) ft) :
    ConstructiveTypeAtoms.FiniteConstruction (field table base width hle ft h) := by
  cases ft
  exact ⟨storage_finite _ _ _ _ _ _, fun _ => trivial⟩

theorem str_finite (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : strtype) (h : StrBound (base+width) st) :
    ConstructiveTypeAtoms.FiniteConstruction (str table base width hle st h) := by
  cases st with
  | DefStructT st =>
    cases st
    exact ⟨each_finite _ _ (field_finite table base width hle) _ _, fun _ => trivial⟩
  | DefArrayT ar =>
    cases ar
    exact ⟨field_finite _ _ _ _ _ _, fun _ => trivial⟩
  | DefFuncT ft =>
    cases ft
    exact ⟨each_finite _ _ (val_finite table base width hle) _ _, fun _ =>
      ⟨each_finite _ _ (val_finite table base width hle) _ _, fun _ => trivial⟩⟩

theorem sub_finite (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (st : SpecTec.subtype) (h : SubBound (base+width) st) :
    ConstructiveTypeAtoms.FiniteConstruction (sub table base width hle st h) := by
  cases st
  exact ⟨each_finite _ _ (heap_finite table base width hle) _ _, fun _ =>
    ⟨str_finite _ _ _ _ _ _, fun _ => trivial⟩⟩

theorem group_finite (table : List deftype) (base : Nat) (hle : base ≤ table.length)
    (sts : List SpecTec.subtype) (h : GroupBound (base+sts.length) sts) :
    ConstructiveTypeAtoms.FiniteConstruction (group table base hle sts h) :=
  ⟨each_finite _ _ (sub_finite table base sts.length hle) _ _, fun _ => trivial⟩

theorem closedIndex_ne_base (table : List deftype) (base width i : Nat)
    (ht : heaptype) (h : Base ht) : closedIndex table base width i ≠ some ht := by
  cases ht <;> simp only [Base] at h <;> try exact h.elim
  all_goals
    simp only [closedIndex, rollTypevar]
    split_ifs <;> simp [substHeaptypeResult, substOfResult, Option.map_eq_some_iff]

/-- Complete leaf inverse, expressed with the unchanged original transformations. -/
theorem heap_exact (table : List deftype) (base width : Nat) (hle : base ≤ table.length)
    (ht : heaptype) (h : HeapBound (base+width) ht) (out : heaptype) :
    Gen.support (heap table base width hle ht h) out ↔
      HeapBound (table.length+width) out ∧
      substHeaptypeResult (rollHeaptype out table.length (table.length+width)) table =
        substHeaptypeResult (rollHeaptype ht base (base+width)) table := by
  rcases raw_cases (base+width) ht h with hb | ⟨i,rfl,hi⟩
  · rw [heap_base table base width hle ht h hb,
      closed_heap_base table base width ht hb, Gen.Support.support_pure]
    constructor
    · rintro rfl
      exact ⟨base_bound _ _ hb, closed_heap_base _ _ _ _ hb⟩
    · rintro ⟨ho,he⟩
      rcases raw_cases (table.length+width) out ho with hbout | ⟨j,rfl,hj⟩
      · rw [closed_heap_base table table.length width out hbout] at he
        exact Option.some.inj he
      · exact False.elim (closedIndex_ne_base table table.length width j ht hb he)
  · constructor
    · intro hg
      simp only [heap, Gen.Support.support_map] at hg
      obtain ⟨j,hj,rfl⟩ := hg
      obtain ⟨hb,he⟩ := (relocate_support table base width hle ⟨i,hi⟩ j).1 hj
      exact ⟨hb,he⟩
    · rintro ⟨ho,he⟩
      rcases raw_cases (table.length+width) out ho with hbout | ⟨j,rfl,hj⟩
      · rw [closed_heap_base table table.length width out hbout] at he
        exact False.elim (closedIndex_ne_base table base width i out hbout he.symm)
      · simp only [heap, Gen.Support.support_map]
        exact ⟨j,(relocate_support table base width hle ⟨i,hi⟩ j).2 ⟨hj,he⟩,rfl⟩

#print axioms group_finite
#print axioms heap_exact
-- OPEN: lift exact closure equality to the whole group and transfer Rectype_ok.
end properties.wasm_module_ok.ConstructiveTypeCopy
