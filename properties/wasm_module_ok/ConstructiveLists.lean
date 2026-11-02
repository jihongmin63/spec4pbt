import properties.wasm_module_ok.ConstructiveGenAudit
import Mathlib.Data.List.Forall2

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveLists
open properties.wasm_module_ok

def exactCount {α : Type} (g : Gen α) : Nat → Gen (List α)
  | 0 => pure []
  | n+1 => do
    let x ← g
    let xs ← exactCount g n
    pure (x::xs)

@[simp] theorem exactCount_support {α : Type} (g : Gen α) (n : Nat) (xs : List α) :
    Gen.support (exactCount g n) xs ↔ xs.length = n ∧ ∀ x ∈ xs, Gen.support g x := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [exactCount]
  | succ n ih => cases xs <;> simp [exactCount, ih, and_assoc, and_left_comm, and_comm]

def all {α : Type} (g : Gen α) : Gen (List α) := do
  let n ← Gen.arbNat
  exactCount g n

@[simp] theorem all_support {α : Type} (g : Gen α) (xs : List α) :
    Gen.support (all g) xs ↔ ∀ x ∈ xs, Gen.support g x := by
  simp [all]

theorem exactCount_audit {α : Type} (g : Gen α)
    (hg : ConstructiveGenAudit.Structural g) (n : Nat) :
    ConstructiveGenAudit.Structural (exactCount g n) := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨hg, fun _ => ⟨ih, fun _ => trivial⟩⟩

theorem all_audit {α : Type} (g : Gen α) (hg : ConstructiveGenAudit.Structural g) :
    ConstructiveGenAudit.Structural (all g) :=
  ⟨ConstructiveGenAudit.arbNat_audit, exactCount_audit g hg⟩

/-- Construct one element for each requested type, with no failing branch. -/
def traverse {α β : Type} (g : α → Gen β) : List α → Gen (List β)
  | [] => pure []
  | x::xs => do
    let y ← g x
    let ys ← traverse g xs
    pure (y::ys)

@[simp] theorem traverse_support {α β : Type} (g : α → Gen β)
    (xs : List α) (ys : List β) : Gen.support (traverse g xs) ys ↔
      List.Forall₂ (fun x y => Gen.support (g x) y) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [traverse]
  | cons x xs ih => cases ys <;> simp [traverse, ih]

theorem traverse_audit {α β : Type} (g : α → Gen β)
    (hg : ∀ x, ConstructiveGenAudit.Structural (g x)) (xs : List α) :
    ConstructiveGenAudit.Structural (traverse g xs) := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨hg x, fun _ => ⟨ih, fun _ => trivial⟩⟩

end properties.wasm_module_ok.ConstructiveLists
