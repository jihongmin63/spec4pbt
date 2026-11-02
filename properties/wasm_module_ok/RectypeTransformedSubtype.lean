import properties.wasm_module_ok.RectypeValidatedSupertypeLength
import properties.wasm_module_ok.SubtypeResultShape

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeTransformedSubtype

open properties.wasm_module_not_ok.Rejection

theorem rectype_ok_appended_transformed_subtype
    (before after : SpecTec.context)
    (sts sts' : List SpecTec.subtype)
    (start finish i : Nat)
    (dts : List SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hafter : after = {before with TYPES := before.TYPES ++ dts})
    (hdts : dts[i]? = some (.DefT (.RecT sts') i)) :
    ∃ hts' : List SpecTec.heaptype,
    ∃ strt' : SpecTec.strtype,
      sts'[i]? = some (.SubT fin hts' strt') ∧
      hts'.length = hts.length := by
  obtain ⟨dtsC, hafterC, hpositions⟩ :=
    RectypeAppendedShape.rectype_ok_appended_position_shape
      before after sts start finish hrect
  obtain ⟨rect', hdtC, hresult⟩ := hpositions i hi
  have hctxEq :
      {before with TYPES := before.TYPES ++ dtsC} =
        {before with TYPES := before.TYPES ++ dts} :=
    hafterC.symm.trans hafter
  have hlistEq : before.TYPES ++ dtsC = before.TYPES ++ dts :=
    congrArg SpecTec.context.TYPES hctxEq
  have hdtsEq : dtsC = dts := List.append_cancel_left hlistEq
  rw [hdtsEq] at hdtC
  have hdefEq : SpecTec.deftype.DefT rect' i = .DefT (.RecT sts') i :=
    Option.some.inj (hdtC.symm.trans hdts)
  have hrectEq : rect' = .RecT sts' := by
    injection hdefEq with heq
  rw [hrectEq] at hresult
  obtain ⟨actual, hrectShape, hsub⟩ :=
    SubstRectypePosition.substRectypeResult_subtypes
      (rollSubtypes sts before.TYPES.length
        (sts.length + before.TYPES.length)) before.TYPES
      (.RecT sts') hresult
  have hactual : actual = sts' := by
    injection hrectShape with heq
    exact heq.symm
  subst actual
  have hrolled :=
    RollSubtypePosition.rollSubtypes_get?_source
      sts before.TYPES.length (sts.length + before.TYPES.length)
      i fin hts strt hsource
  have hirolled :
      i < (rollSubtypes sts before.TYPES.length
        (sts.length + before.TYPES.length)).length := by
    simpa [rollSubtypes] using hi
  obtain ⟨src, dst, hsrc, hdst, hsubst⟩ :=
    SubstSubtypeListPosition.substSubtypeListResult_position
      (rollSubtypes sts before.TYPES.length
        (sts.length + before.TYPES.length)) before.TYPES sts' i hsub hirolled
  have hsrcEq :
      src = .SubT fin
        (rollHeaptypes hts before.TYPES.length
          (sts.length + before.TYPES.length))
        (rollStrtype strt before.TYPES.length
          (sts.length + before.TYPES.length)) :=
    Option.some.inj (hsrc.symm.trans hrolled)
  subst src
  obtain ⟨hts', strt', hshape, _⟩ :=
    SubtypeResultShape.substSubtypeResult_supertype_shape
      fin
      (rollHeaptypes hts before.TYPES.length
        (sts.length + before.TYPES.length))
      (rollStrtype strt before.TYPES.length
        (sts.length + before.TYPES.length))
      before.TYPES dst hsubst
  subst dst
  refine ⟨hts', strt', hdst, ?_⟩
  exact RectypeValidatedSupertypeLength.rectype_ok_appended_supertype_length
    before after sts sts' start finish i dts fin hts hts' strt strt'
    hrect hi hsource hafter hdts hdst

end properties.wasm_module_ok.RectypeTransformedSubtype
