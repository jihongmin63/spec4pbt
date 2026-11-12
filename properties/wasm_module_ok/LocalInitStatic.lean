import properties.wasm_module_ok.LocalInitValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.LocalInitStatic

private theorem initLocalResult_static_fields
    (c c₁ : SpecTec.context) (x : SpecTec.localidx)
    (h : LocalInitValidation.initLocalResult c x = some c₁) :
    c₁.TYPES = c.TYPES ∧
    c₁.FUNCS = c.FUNCS ∧
    c₁.GLOBALS = c.GLOBALS ∧
    c₁.REFS = c.REFS := by
  cases hget : c.LOCALS[x]? with
  | none => simp [LocalInitValidation.initLocalResult, hget] at h
  | some localType =>
    cases localType with
    | LocalT init t =>
      simp [LocalInitValidation.initLocalResult, hget] at h
      subst c₁
      simp

private theorem initLocalsResult_static_fields
    (c c₁ : SpecTec.context) (indices : List SpecTec.localidx)
    (h : LocalInitValidation.initLocalsResult c indices = some c₁) :
    c₁.TYPES = c.TYPES ∧
    c₁.FUNCS = c.FUNCS ∧
    c₁.GLOBALS = c.GLOBALS ∧
    c₁.REFS = c.REFS := by
  induction indices generalizing c with
  | nil =>
    simp [LocalInitValidation.initLocalsResult] at h
    subst c₁
    exact ⟨rfl, rfl, rfl, rfl⟩
  | cons x xs ih =>
    cases hhead : LocalInitValidation.initLocalResult c x with
    | none =>
      simp [LocalInitValidation.initLocalsResult, hhead] at h
    | some middle =>
      have htail : LocalInitValidation.initLocalsResult middle xs = some c₁ := by
        simpa [LocalInitValidation.initLocalsResult, hhead] using h
      obtain ⟨ht₁, hf₁, hg₁, hr₁⟩ :=
        initLocalResult_static_fields c middle x hhead
      obtain ⟨ht₂, hf₂, hg₂, hr₂⟩ := ih middle htail
      exact ⟨ht₂.trans ht₁, hf₂.trans hf₁,
        hg₂.trans hg₁, hr₂.trans hr₁⟩

theorem init_locals_static_fields
    (c c₁ : SpecTec.context) (indices : List SpecTec.idx)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.«$init_locals» c indices⟩)
      start (.success (.of c₁)) fin) :
    c₁.TYPES = c.TYPES ∧
    c₁.FUNCS = c.FUNCS ∧
    c₁.GLOBALS = c.GLOBALS ∧
    c₁.REFS = c.REFS := by
  exact initLocalsResult_static_fields c c₁ indices
    ((LocalInitValidation.init_locals_success_iff_result
      c indices c₁ start fin).1 h).1

end properties.wasm_module_ok.LocalInitStatic
