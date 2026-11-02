import properties.wasm_module_ok.Generator

set_option autoImplicit false
namespace properties.wasm_module_ok.PositiveIndexAudit

/-- Legacy audit interface retained for callers. Unlike the constructive audit,
this predicate alone permits assume and does not establish absence of screening. -/
def Lawful {α : Type} : Gen α → Prop
  | .ret _ => True
  | .pick a b => Lawful a ∧ Lawful b
  | .bind a k => Lawful a ∧ ∀ x, Lawful (k x)
  | .assume _ k => ∀ h, Lawful (k h)
  | .indexed f => (∀ n, Lawful (f n)) ∧
      ∀ v n k, Gen.support (f n) (some v) → Gen.support (f (n + k)) (some v)

theorem structural_lawful {α : Type} (g : Gen α) (h : ConstructiveGenAudit.Structural g) : Lawful g := by
  induction g with
  | ret _ => trivial
  | pick a b ia ib => exact ⟨ia h.1,ib h.2⟩
  | bind a k ia ik => exact ⟨ia h.1,fun x => ik x (h.2 x)⟩
  | assume _ _ _ => exact h.elim
  | indexed f ih => exact ⟨fun n => ih n (h.1 n),h.2⟩

theorem lawful_generator : Lawful Generator.generator := structural_lawful _ Generator.structural

end properties.wasm_module_ok.PositiveIndexAudit
