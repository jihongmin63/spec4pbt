/- Property-local positive runtime refinement for the unchanged Wasm specification.
   Original source identity: s41537f07a12c318563e6aabf63ee533b7bcdb33a44bfeb071c4af4b8ddd8bf9a.
   Executable definitions and erasure proofs are separate; no compiler replacements. -/
import properties.wasm_module_ok.PositiveBody
import properties.wasm_module_ok.PositiveSound
namespace properties.wasm_module_ok.PositiveRuntime
open SpecTecExecution
set_option autoImplicit false
set_option maxRecDepth 10000

/-- True is a witnessed successful bounded run. False is only absence of a
successful result at this fuel; it does not assert semantic rejection. -/
def accepts (fuel : Nat) (m : SpecTec.module) : Bool :=
  match run fuel (.call (.Module_ok m)) 0 with
  | .done (.success ()) _ => true
  | _ => false

theorem accepts_sound (fuel : Nat) (m : SpecTec.module)
    (h : accepts fuel m = true) : SpecTec.Module_ok m := by
  unfold accepts at h
  cases hr : run fuel (.call (.Module_ok m)) 0 with
  | outOfFuel => simp [hr] at h
  | unsupportedPrimitive => simp [hr] at h
  | done outcome final =>
    cases outcome with
    | unmatch => simp [hr] at h
    | abort msg => simp [hr] at h
    | success u =>
      cases u
      exact ⟨final, sound body_correct fuel _ _ _ _ hr⟩

theorem accepts_complete (m : SpecTec.module) (h : SpecTec.Module_ok m) :
    ∃ fuel, accepts fuel m = true := by
  obtain ⟨final, h⟩ := h
  obtain ⟨fuel, outcome, he, hr⟩ := complete body_correct h
    (.call (.Module_ok m)) rfl
  cases outcome with
  | unmatch => cases he
  | abort msg => cases he
  | success u =>
    cases u
    exact ⟨fuel, by simp [accepts, hr]⟩

theorem accepts_mono {fuel more : Nat} (le : fuel ≤ more) (m : SpecTec.module)
    (h : accepts fuel m = true) : accepts more m = true := by
  unfold accepts at h ⊢
  cases hr : run fuel (.call (.Module_ok m)) 0 with
  | outOfFuel => simp [hr] at h
  | unsupportedPrimitive => simp [hr] at h
  | done outcome final =>
    cases outcome with
    | unmatch => simp [hr] at h
    | abort msg => simp [hr] at h
    | success u =>
      cases u
      rw [mono le _ _ _ _ hr]

theorem accepts_iff (m : SpecTec.module) :
    (∃ fuel, accepts fuel m = true) ↔ SpecTec.Module_ok m :=
  ⟨fun ⟨fuel, h⟩ => accepts_sound fuel m h, accepts_complete m⟩

end properties.wasm_module_ok.PositiveRuntime
