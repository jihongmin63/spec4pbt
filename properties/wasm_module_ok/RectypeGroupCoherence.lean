import properties.wasm_module_ok.UnrollPositionBridge
import properties.wasm_module_ok.RectypeAppendedShape
import properties.wasm_module_ok.SubstRectypeLength

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeGroupCoherence

open properties.wasm_module_not_ok.Rejection

theorem rectype_ok_appended_group_coherent
    (before after : SpecTec.context)
    (sts : List SpecTec.subtype) (start finish : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish) :
    ∃ dts : List SpecTec.deftype,
    ∃ sts' : List SpecTec.subtype,
      after = {before with TYPES := before.TYPES ++ dts} ∧
      sts'.length = sts.length ∧
      (∀ i, i < sts.length → dts[i]? = some (.DefT (.RecT sts') i)) := by
  obtain ⟨dts, hafter, hpositions⟩ :=
    RectypeAppendedShape.rectype_ok_appended_position_shape
      before after sts start finish hrect
  cases sts with
  | nil =>
      refine ⟨dts, [], hafter, rfl, ?_⟩
      intro i hi
      simp at hi
  | cons st rest =>
      obtain ⟨rect', hget, hresult⟩ := hpositions 0 (by simp)
      obtain ⟨sts', hrectEq, hlen⟩ :=
        SubstRectypeLength.substRectypeResult_length
          (rollSubtypes (st :: rest) before.TYPES.length
            ((st :: rest).length + before.TYPES.length))
          before.TYPES rect' hresult
      subst rect'
      refine ⟨dts, sts', hafter, ?_, ?_⟩
      · simpa [rollSubtypes] using hlen
      · intro i hi
        obtain ⟨rectI, hgetI, hresultI⟩ := hpositions i hi
        have hrectI : rectI = .RecT sts' := by
          exact Option.some.inj (hresultI.symm.trans hresult)
        subst rectI
        exact hgetI

end properties.wasm_module_ok.RectypeGroupCoherence
