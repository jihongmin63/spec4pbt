import properties.wasm_module_ok.RectypeAppendedPosition
import properties.wasm_module_not_ok.DeftypeSubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeAppendedShape

open properties.wasm_module_not_ok.Rejection

theorem subst_deftype_result_shape
    (rect : SpecTec.rectype) (i : Nat)
    (dts : List SpecTec.deftype) (dt' : SpecTec.deftype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.deftype,
        SpecTec.Call.«$subst_deftype»
          (List SpecTec.deftype) dts
          SpecTec.Call.«$subst_of» (.DefT rect i)⟩)
      start (.success (.of dt')) finish) :
    ∃ rect' : SpecTec.rectype,
      dt' = .DefT rect' i ∧
      substRectypeResult rect dts = some rect' := by
  obtain ⟨hout, _⟩ := subst_deftype_of_deterministic
    (.DefT rect i) dts start finish (.success (.of dt')) h
  cases hresult : substRectypeResult rect dts with
  | none =>
      simp [substDeftypeResult, hresult, optionOutcome] at hout
  | some rect' =>
      simp [substDeftypeResult, hresult, optionOutcome] at hout
      cases hout
      exact ⟨rect', rfl, rfl⟩

theorem rectype_ok_appended_position_shape
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish) :
    ∃ dts : List SpecTec.deftype,
      c' = {c with TYPES := c.TYPES ++ dts} ∧
      ∀ i, i < sts.length →
        ∃ rect' : SpecTec.rectype,
          dts[i]? = some (.DefT rect' i) ∧
          substRectypeResult
            (.RecT (rollSubtypes sts c.TYPES.length
              (sts.length + c.TYPES.length))) c.TYPES = some rect' := by
  obtain ⟨dts, hc, hpos⟩ :=
    properties.wasm_module_ok.RectypeAppendedPosition.rectype_ok_appended_position_subst
      c c' sts start finish h
  refine ⟨dts, hc, ?_⟩
  intro i hi
  obtain ⟨dt', hget, before, after, hcall⟩ := hpos i hi
  obtain ⟨rect', hshape, hresult⟩ :=
    subst_deftype_result_shape
      (.RecT (rollSubtypes sts c.TYPES.length
        (sts.length + c.TYPES.length))) i c.TYPES dt'
      before after hcall
  subst dt'
  exact ⟨rect', hget, hresult⟩

end properties.wasm_module_ok.RectypeAppendedShape
