import properties.wasm_module_ok.ConstructiveGenAudit

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeSkeleton
open properties.wasm_module_ok

/-- The structural kind is chosen before any signature fields. -/
inductive Kind where
  | structK | arrayK | funcK
  deriving DecidableEq, Repr

structure Header where
  finality : SpecTec.final
  kind : Kind
  deriving DecidableEq

structure Entry where
  header : Header
  parent : Option Nat
  deriving DecidableEq

/-- Enumerate eligible indices from existing metadata, without constructing or
checking a candidate subtype. The source permits at most one declared parent. -/
def parentOptions : List Header → List (Nat × Kind)
  | [] => []
  | h :: hs =>
    let rest := (parentOptions hs).map fun p => (p.1 + 1, p.2)
    match h.finality with
    | .Final => rest
    | .NoFinal => (0, h.kind) :: rest

theorem parentOptions_exact (hs : List Header) (i : Nat) (k : Kind) :
    (i, k) ∈ parentOptions hs ↔
      ∃ h, hs[i]? = some h ∧ h.finality = .NoFinal ∧ h.kind = k := by
  induction hs generalizing i with
  | nil => simp [parentOptions]
  | cons h hs ih =>
    cases h with
    | mk f hk =>
      cases f <;> cases i <;>
        simp [parentOptions, ih, Prod.ext_iff, eq_comm]

def parents (hs : List Header) : Gen (Option (Nat × Kind)) :=
  ConstructiveTypeAtoms.choose none ((parentOptions hs).map some)

def kinds : Gen Kind :=
  ConstructiveTypeAtoms.choose .structK [.arrayK, .funcK]

@[simp] theorem kinds_support (k : Kind) : Gen.support kinds k := by
  cases k <;> simp [kinds]

def finalities : Gen SpecTec.final :=
  ConstructiveTypeAtoms.choose .Final [.NoFinal]

@[simp] theorem finalities_support (f : SpecTec.final) :
    Gen.support finalities f := by
  cases f <;> simp [finalities]

def entry (hs : List Header) : Gen Entry := do
  let f ← finalities
  let p ← parents hs
  match p with
  | none =>
    let k ← kinds
    pure ⟨⟨f, k⟩, none⟩
  | some (i, k) => pure ⟨⟨f, k⟩, some i⟩

def EntryAllowed (hs : List Header) (e : Entry) : Prop :=
  match e.parent with
  | none => True
  | some i => ∃ h, hs[i]? = some h ∧ h.finality = .NoFinal ∧
      h.kind = e.header.kind

theorem entry_support (hs : List Header) (e : Entry) :
    Gen.support (entry hs) e ↔ EntryAllowed hs e := by
  cases e with
  | mk h p =>
    cases h with
    | mk f k =>
      cases p with
      | none => simp [entry, parents, EntryAllowed]
      | some i =>
        simp only [entry, Gen.Support.support_bind, finalities_support, true_and,
          parents, ConstructiveTypeAtoms.support_choose, List.mem_cons,
          List.mem_map, Option.some.injEq, Prod.exists,
          parentOptions_exact, or_and_right, exists_or,
          exists_eq_left, EntryAllowed]
        simp only [Gen.Support.support_bind, Gen.Support.support_pure, kinds_support,
          true_and, Entry.mk.injEq, Header.mk.injEq,
          reduceCtorEq, and_false, exists_false, false_or]
        constructor
        · rintro ⟨f', p, ⟨i', k', h, rfl⟩, hout⟩
          have heq : (⟨⟨f, k⟩, some i⟩ : Entry) = ⟨⟨f', k'⟩, some i'⟩ := hout
          cases heq
          exact h
        · intro h
          exact ⟨f, some (i, k), ⟨i, k, h, rfl⟩, rfl⟩

def Allowed : List Header → List Entry → Prop
  | _, [] => True
  | hs, e :: es => EntryAllowed hs e ∧ Allowed (hs ++ [e.header]) es

def exactCount : Nat → List Header → Gen (List Entry)
  | 0, _ => pure []
  | n + 1, hs => do
    let e ← entry hs
    let es ← exactCount n (hs ++ [e.header])
    pure (e :: es)

theorem exactCount_support (n : Nat) (hs : List Header) (es : List Entry) :
    Gen.support (exactCount n hs) es ↔ es.length = n ∧ Allowed hs es := by
  induction n generalizing hs es with
  | zero => cases es <;> simp [exactCount, Allowed]
  | succ n ih =>
    cases es <;> simp [exactCount, entry_support, ih, Allowed,
      and_assoc, and_left_comm, and_comm]

/-- Every finite parent forest with earlier non-final, same-kind parents is
covered. Signature variance and original Rectype_ok are separate obligations. -/
def skeleton (hs : List Header) : Gen (List Entry) := do
  let n ← Gen.arbNat
  exactCount n hs

theorem skeleton_support (hs : List Header) (es : List Entry) :
    Gen.support (skeleton hs) es ↔ Allowed hs es := by
  simp [skeleton, exactCount_support]

theorem entry_audit (hs : List Header) : ConstructiveGenAudit.Structural (entry hs) := by
  refine ⟨ConstructiveGenAudit.finite_audit _
    (ConstructiveTypeAtoms.finite_choose _ _), ?_⟩
  intro f
  refine ⟨ConstructiveGenAudit.finite_audit _
    (ConstructiveTypeAtoms.finite_choose _ _), ?_⟩
  intro p
  cases p with
  | none => exact ⟨ConstructiveGenAudit.finite_audit _
      (ConstructiveTypeAtoms.finite_choose _ _), fun _ => trivial⟩
  | some p => cases p; trivial

theorem exactCount_audit (n : Nat) (hs : List Header) :
    ConstructiveGenAudit.Structural (exactCount n hs) := by
  induction n generalizing hs with
  | zero => trivial
  | succ n ih => exact ⟨entry_audit hs, fun e => ⟨ih _, fun _ => trivial⟩⟩

theorem skeleton_audit (hs : List Header) :
    ConstructiveGenAudit.Structural (skeleton hs) :=
  ⟨ConstructiveGenAudit.arbNat_audit, fun n => exactCount_audit n hs⟩

theorem skeleton_total (hs : List Header) : Gen.total (skeleton hs) :=
  ConstructiveGenAudit.audit_total _ (skeleton_audit hs)

theorem empty_completion (hs : List Header) : Gen.support (skeleton hs) [] := by
  rw [skeleton_support]
  trivial

end properties.wasm_module_ok.ConstructiveTypeSkeleton
