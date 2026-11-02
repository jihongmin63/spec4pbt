import properties.wasm_module_ok.RectypeSupertypeLength

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeValidatedSupertypeLength

theorem rectype_ok_appended_supertype_length
    (before after : SpecTec.context)
    (sts sts' : List SpecTec.subtype)
    (start finish i : Nat)
    (dts : List SpecTec.deftype)
    (fin : SpecTec.final) (hts hts' : List SpecTec.heaptype)
    (strt strt' : SpecTec.strtype)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hafter : after = {before with TYPES := before.TYPES ++ dts})
    (hdts : dts[i]? = some (.DefT (.RecT sts') i))
    (htrans : sts'[i]? = some (.SubT fin hts' strt')) :
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
  exact RectypeSupertypeLength.rectype_subst_supertype_length
    sts sts' before.TYPES before.TYPES.length
    (sts.length + before.TYPES.length) i
    fin hts hts' strt strt' hresult hsource htrans

end properties.wasm_module_ok.RectypeValidatedSupertypeLength
