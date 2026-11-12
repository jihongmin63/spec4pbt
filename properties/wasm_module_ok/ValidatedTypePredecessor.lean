import properties.wasm_module_ok.ValidatedTypeActualEdges

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedTypePredecessor

theorem rectype_predecessor_lookup
    (before after c : SpecTec.context)
    (sts : List SpecTec.subtype) (start finish i k : Nat)
    (dts tail : List SpecTec.deftype)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hafter : after = {before with TYPES := before.TYPES ++ dts})
    (hprefix : c.TYPES = after.TYPES ++ tail)
    (hcase :
      (∃ dt : SpecTec.deftype,
        k < before.TYPES.length ∧ before.TYPES[k]? = some dt) ∨
      (before.TYPES.length ≤ k ∧ k - before.TYPES.length < i)) :
    (∃ dt : SpecTec.deftype,
      k < before.TYPES.length ∧
      before.TYPES[k]? = some dt ∧ c.TYPES[k]? = some dt) ∨
    (∃ q : Nat, ∃ stsQ : List SpecTec.subtype,
      k = before.TYPES.length + q ∧ q < i ∧
      c.TYPES[k]? = some (.DefT (.RecT stsQ) q)) := by
  have carryLookup (n : Nat) (dt : SpecTec.deftype)
      (hn : n < after.TYPES.length)
      (hlookup : after.TYPES[n]? = some dt) :
      c.TYPES[n]? = some dt := by
    rw [hprefix, List.getElem?_append_left hn]
    exact hlookup
  rcases hcase with ⟨dt, hk, hlookup⟩ | ⟨hge, hdiff⟩
  · have hkAfter : k < after.TYPES.length := by
      rw [hafter, List.length_append]
      omega
    have hlookupAfter : after.TYPES[k]? = some dt := by
      rw [hafter, List.getElem?_append_left hk]
      exact hlookup
    exact Or.inl ⟨dt, hk, hlookup,
      carryLookup k dt hkAfter hlookupAfter⟩
  · let q := k - before.TYPES.length
    have hq : q < i := hdiff
    have hqSts : q < sts.length := by omega
    obtain ⟨dtsQ, hafterQ, hpositions⟩ :=
      SubstRectypeLength.rectype_ok_appended_inner_length
        before after sts start finish hrect
    obtain ⟨stsQ, hdtsQ, _⟩ := hpositions q hqSts
    have hctxEq :
        {before with TYPES := before.TYPES ++ dtsQ} =
          {before with TYPES := before.TYPES ++ dts} :=
      hafterQ.symm.trans hafter
    have hlistEq : before.TYPES ++ dtsQ = before.TYPES ++ dts :=
      congrArg SpecTec.context.TYPES hctxEq
    have hdtEq : dtsQ = dts := List.append_cancel_left hlistEq
    rw [hdtEq] at hdtsQ
    have hqDts : q < dts.length :=
      (List.getElem?_eq_some_iff.mp hdtsQ).choose
    have hkEq : k = before.TYPES.length + q := by
      dsimp [q]
      omega
    have hkAfter : k < after.TYPES.length := by
      rw [hkEq, hafter, List.length_append]
      omega
    have hlookupAfter :
        after.TYPES[k]? = some (.DefT (.RecT stsQ) q) := by
      rw [hkEq, hafter]
      rw [List.getElem?_append_right (by omega)]
      have hidx : before.TYPES.length + q - before.TYPES.length = q := by
        omega
      rw [hidx]
      exact hdtsQ
    exact Or.inr ⟨q, stsQ, hkEq, hq,
      carryLookup k (.DefT (.RecT stsQ) q) hkAfter hlookupAfter⟩

end properties.wasm_module_ok.ValidatedTypePredecessor
