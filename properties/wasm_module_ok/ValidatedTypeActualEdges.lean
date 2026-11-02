import properties.wasm_module_ok.ValidatedTypeLookup

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedTypeActualEdges

open properties.wasm_module_ok.ValidatedTypeChain

theorem validated_types_position_actual_edges
    (c : SpecTec.context) (p : Nat)
    (hc : ValidatedTypes c) (hp : p < c.TYPES.length) :
    ∃ before after : SpecTec.context,
    ∃ sts : List SpecTec.subtype,
    ∃ start finish i : Nat,
    ∃ tail : List SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strt : SpecTec.strtype,
    ∃ dts : List SpecTec.deftype,
    ∃ sts' : List SpecTec.subtype,
      ValidatedTypes before ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context,
          SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
        start (.success (.of after)) finish ∧
      p = before.TYPES.length + i ∧ i < sts.length ∧
      sts[i]? = some (.SubT fin hts strt) ∧
      after = {before with TYPES := before.TYPES ++ dts} ∧
      dts[i]? = some (.DefT (.RecT sts') i) ∧
      c.TYPES = after.TYPES ++ tail ∧
      c.TYPES[p]? = some (.DefT (.RecT sts') i) ∧
      ∀ j, j < hts.length →
        ∃ k : Nat,
        ∃ hts' : List SpecTec.heaptype,
        ∃ strt' : SpecTec.strtype,
          hts[j]? = some (.VarHT (.StatX k)) ∧
          k < p ∧
          sts'[i]? = some (.SubT fin hts' strt') ∧
          ((∃ dt : SpecTec.deftype,
              k < before.TYPES.length ∧ before.TYPES[k]? = some dt ∧
              hts'[j]? = some (.DefHT dt)) ∨
            (before.TYPES.length ≤ k ∧ k - before.TYPES.length < i ∧
              hts'[j]? = some (.VarHT (.RecX (k - before.TYPES.length))))) := by
  obtain ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, dts, sts', hbefore, hrect,
    hpos, hi, hsource, hafter, hdts, _hafterLookup, hprefix, hcLookup⟩ :=
    ValidatedTypeLookup.validated_types_position_lookup c p hc hp
  refine ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, dts, sts', hbefore, hrect,
    hpos, hi, hsource, hafter, hdts, hprefix, hcLookup, ?_⟩
  intro j hj
  obtain ⟨k, hstatic, hlt, dtsEdge, stsEdge, htsEdge, strtEdge,
      hafterEdge, hdtsEdge, hstsEdge, hcase⟩ :=
    ActualAllSupertypeCases.rectype_ok_appended_all_supertype_cases
      before after sts start finish i j fin hts strt
      hrect hi hsource hj
  have hctxEq :
      {before with TYPES := before.TYPES ++ dtsEdge} =
        {before with TYPES := before.TYPES ++ dts} :=
    hafterEdge.symm.trans hafter
  have hlistEq : before.TYPES ++ dtsEdge = before.TYPES ++ dts :=
    congrArg SpecTec.context.TYPES hctxEq
  have hdtEq : dtsEdge = dts := List.append_cancel_left hlistEq
  rw [hdtEq] at hdtsEdge
  have hdefEq :
      SpecTec.deftype.DefT (.RecT stsEdge) i = .DefT (.RecT sts') i :=
    Option.some.inj (hdtsEdge.symm.trans hdts)
  have hstsEq : stsEdge = sts' := by
    injection hdefEq with hrectEq
    injection hrectEq with hstsEq
  rw [hstsEq] at hstsEdge
  refine ⟨k, htsEdge, strtEdge, hstatic, ?_, hstsEdge, hcase⟩
  omega

end properties.wasm_module_ok.ValidatedTypeActualEdges
