import properties.wasm_module_ok.SubstRectypeLength

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedGroupUniform

open properties.wasm_module_not_ok.Rejection

/-- Every definition appended by one successful recursive-group check refers
to the same substituted recursive type. -/
theorem rectype_ok_uniform_appended
    (before after : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish) :
    ∃ dts : List SpecTec.deftype,
    ∃ sts' : List SpecTec.subtype,
      after = {before with TYPES := before.TYPES ++ dts} ∧
      sts'.length = sts.length ∧
      ∀ j, j < sts.length →
        dts[j]? = some (.DefT (.RecT sts') j) := by
  obtain ⟨dts, hafter, hpositions⟩ :=
    RectypeAppendedShape.rectype_ok_appended_position_shape
      before after sts start finish hrect
  let rolled := rollSubtypes sts before.TYPES.length
    (sts.length + before.TYPES.length)
  cases hresult : substRectypeResult (.RecT rolled) before.TYPES with
  | none =>
      cases sts with
      | nil =>
          simp [rolled, rollSubtypes, substRectypeResult,
            substSubtypeListResult] at hresult
      | cons st rest =>
          obtain ⟨rect', _, hsome⟩ := hpositions 0 (by simp)
          rw [hresult] at hsome
          contradiction
  | some rect' =>
      obtain ⟨sts', hshape, hlen⟩ :=
        SubstRectypeLength.substRectypeResult_length
          rolled before.TYPES rect' hresult
      subst rect'
      refine ⟨dts, sts', hafter, ?_, ?_⟩
      · simpa [rolled, rollSubtypes] using hlen
      · intro j hj
        obtain ⟨other, hget, hother⟩ := hpositions j hj
        have heq : other = .RecT sts' := by
          rw [hresult] at hother
          exact Option.some.inj hother.symm
        simpa [heq] using hget

/-- A later type table retains every definition from the validated group at
its original absolute position. -/
theorem rectype_ok_uniform_in_extension
    (before after c : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat) (tail : List SpecTec.deftype)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hprefix : c.TYPES = after.TYPES ++ tail) :
    ∃ sts' : List SpecTec.subtype,
      sts'.length = sts.length ∧
      ∀ j, j < sts.length →
        c.TYPES[before.TYPES.length + j]? =
          some (.DefT (.RecT sts') j) := by
  obtain ⟨dts, sts', hafter, hlen, hpositions⟩ :=
    rectype_ok_uniform_appended before after sts start finish hrect
  refine ⟨sts', hlen, ?_⟩
  intro j hj
  have hget := hpositions j hj
  have hjDts : j < dts.length :=
    (List.getElem?_eq_some_iff.mp hget).choose
  have hjAfter : before.TYPES.length + j < after.TYPES.length := by
    rw [hafter, List.length_append]
    omega
  rw [hprefix, List.getElem?_append_left hjAfter, hafter]
  rw [List.getElem?_append_right (by omega)]
  simpa using hget

end properties.wasm_module_ok.ValidatedGroupUniform
