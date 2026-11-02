import properties.wasm_module_ok.RectypeGroupCoherence

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeLocalLookup

theorem rectype_ok_local_same_group_lookup
    (before after c : SpecTec.context)
    (sts sts' : List SpecTec.subtype)
    (start finish i q : Nat)
    (dts tail : List SpecTec.deftype)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length) (hq : q < i)
    (hafter : after = {before with TYPES := before.TYPES ++ dts})
    (hcurrent : dts[i]? = some (.DefT (.RecT sts') i))
    (hprefix : c.TYPES = after.TYPES ++ tail) :
    c.TYPES[before.TYPES.length + q]? =
      some (.DefT (.RecT sts') q) := by
  obtain ⟨dtsC, stsC, hafterC, _hlen, hpositions⟩ :=
    RectypeGroupCoherence.rectype_ok_appended_group_coherent
      before after sts start finish hrect
  have hctxEq :
      {before with TYPES := before.TYPES ++ dtsC} =
        {before with TYPES := before.TYPES ++ dts} :=
    hafterC.symm.trans hafter
  have hlistEq : before.TYPES ++ dtsC = before.TYPES ++ dts :=
    congrArg SpecTec.context.TYPES hctxEq
  have hdtsEq : dtsC = dts := List.append_cancel_left hlistEq
  rw [hdtsEq] at hpositions
  have hcurrentC := hpositions i hi
  have hdefEq :
      SpecTec.deftype.DefT (.RecT stsC) i = .DefT (.RecT sts') i :=
    Option.some.inj (hcurrentC.symm.trans hcurrent)
  have hstsEq : stsC = sts' := by
    injection hdefEq with hrectEq
    injection hrectEq with hstsEq
  rw [hstsEq] at hpositions
  have hqSts : q < sts.length := by omega
  have hqDts := hpositions q hqSts
  have hqBound : q < dts.length :=
    (List.getElem?_eq_some_iff.mp hqDts).choose
  have hqAfter : before.TYPES.length + q < after.TYPES.length := by
    rw [hafter, List.length_append]
    omega
  have hqAfterLookup :
      after.TYPES[before.TYPES.length + q]? =
        some (.DefT (.RecT sts') q) := by
    rw [hafter]
    rw [List.getElem?_append_right (by omega)]
    have hidx : before.TYPES.length + q - before.TYPES.length = q := by
      omega
    rw [hidx]
    exact hqDts
  rw [hprefix, List.getElem?_append_left hqAfter]
  exact hqAfterLookup

end properties.wasm_module_ok.RectypeLocalLookup
