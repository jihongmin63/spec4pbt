import properties.wasm_module_ok.ConstructiveTypeAtoms
import Palamedes.Data.Nat

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveGenAudit

/-- A structural audit, including every continuation and every indexed family.
It does not inspect host functions: those still require review for screening. -/
def Structural {α : Type} : Gen α → Prop
  | .ret _ => True
  | .pick a b => Structural a ∧ Structural b
  | .bind a k => Structural a ∧ ∀ x, Structural (k x)
  | .assume _ _ => False
  | .indexed f => (∀ n, Structural (f n)) ∧
      ∀ v n k, Gen.support (f n) (some v) → Gen.support (f (n + k)) (some v)

theorem structural_indexLawful {α : Type} (g : Gen α) (h : Structural g) :
    Gen.IndexLawful g := by
  induction g with
  | ret _ => trivial
  | pick a b ia ib => exact ⟨ia h.1, ib h.2⟩
  | bind a k ia ik => exact ⟨ia h.1, fun x => ik x (h.2 x)⟩
  | assume _ _ _ => exact h.elim
  | indexed f ih => exact ⟨fun n => ih n (h.1 n), h.2⟩

@[simp] theorem pure_audit {α : Type} (a : α) : Structural (pure a : Gen α) := trivial
@[simp] theorem pick_audit {α : Type} (a b : Gen α) :
    Structural (Gen.pick a b) ↔ Structural a ∧ Structural b := Iff.rfl
@[simp] theorem bind_audit {α β : Type} (a : Gen α) (k : α → Gen β) :
    Structural (a >>= k) ↔ Structural a ∧ ∀ x, Structural (k x) := Iff.rfl
@[simp] theorem map_audit {α β : Type} (f : α → β) (a : Gen α) :
    Structural (f <$> a) ↔ Structural a := by
  change (Structural a ∧ ∀ _, True) ↔ Structural a
  simp

@[simp] theorem arbNat_audit : Structural Gen.arbNat := by
  unfold Gen.arbNat
  constructor
  · intro n
    induction n with
    | zero => trivial
    | succ n ih =>
      simpa only [Gen.arbNatAux, pick_audit, pure_audit, map_audit, true_and] using ih
  · exact fun _ _ _ h => Gen.arbNatAux_monotonic h

theorem finite_audit {α : Type} (g : Gen α)
    (h : ConstructiveTypeAtoms.FiniteConstruction g) : Structural g := by
  induction g with
  | ret _ => trivial
  | pick a b ia ib => exact ⟨ia h.1, ib h.2⟩
  | bind a k ia ik => exact ⟨ia h.1, fun x => ik x (h.2 x)⟩
  | assume _ _ _ => exact h.elim
  | indexed _ _ => exact h.elim

theorem audit_total {α : Type} (g : Gen α) (h : Structural g) : Gen.total g := by
  induction g with
  | ret _ => trivial
  | pick a b ia ib => exact ⟨ia h.1, ib h.2⟩
  | bind a k ia ik => exact ⟨ia h.1, fun x _ => ik x (h.2 x)⟩
  | assume _ _ _ => exact h.elim
  | indexed f ih => exact fun n => ih n (h.1 n)

end properties.wasm_module_ok.ConstructiveGenAudit
