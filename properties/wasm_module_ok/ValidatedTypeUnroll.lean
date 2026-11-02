import properties.wasm_module_ok.ValidatedTypeLookup
import properties.wasm_module_ok.UnrollInterface

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedTypeUnroll

open properties.wasm_module_ok.ValidatedTypeChain
open properties.wasm_module_not_ok.Rejection

theorem validated_types_position_unrolls
    (c : SpecTec.context) (p start : Nat)
    (hc : ValidatedTypes c) (hp : p < c.TYPES.length) :
    ∃ dt : SpecTec.deftype, ∃ st : SpecTec.subtype,
      c.TYPES[p]? = some dt ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dt⟩)
        start (.success (.of st)) start := by
  obtain ⟨before, after, sts, rectStart, rectFinish, i, tail,
    fin, hts, strt, dts, sts', _hbefore, hrect,
    _hpos, hi, _hsource, hafter, hdts, _hafterLookup, _hprefix, hcLookup⟩ :=
    ValidatedTypeLookup.validated_types_position_lookup c p hc hp
  obtain ⟨dtsAlt, hafterAlt, hpositions⟩ :=
    SubstRectypeLength.rectype_ok_appended_inner_length
      before after sts rectStart rectFinish hrect
  obtain ⟨stsAlt, hdtsAlt, hlen⟩ := hpositions i hi
  have hctxEq :
      {before with TYPES := before.TYPES ++ dtsAlt} =
        {before with TYPES := before.TYPES ++ dts} :=
    hafterAlt.symm.trans hafter
  have hlistEq : before.TYPES ++ dtsAlt = before.TYPES ++ dts :=
    congrArg SpecTec.context.TYPES hctxEq
  have hdtsEq : dtsAlt = dts := List.append_cancel_left hlistEq
  rw [hdtsEq] at hdtsAlt
  have hdefEq :
      SpecTec.deftype.DefT (.RecT stsAlt) i = .DefT (.RecT sts') i :=
    Option.some.inj (hdtsAlt.symm.trans hdts)
  have hstsEq : stsAlt = sts' := by
    injection hdefEq with hrectEq
    injection hrectEq with hstsEq
  rw [hstsEq] at hlen
  have hi' : i < sts'.length := by omega
  have hu : i < (unrollSubtypes sts' (.RecT sts')).length := by
    simpa [unrollSubtypes] using hi'
  cases hget : (unrollSubtypes sts' (.RecT sts'))[i]? with
  | none =>
      have hnone := List.getElem?_eq_none_iff.mp hget
      omega
  | some st =>
      have hresult :
          unrollDeftypeResult (.DefT (.RecT sts') i) = some st := by
        simpa [unrollDeftypeResult, unrollRectype] using hget
      exact ⟨.DefT (.RecT sts') i, st, hcLookup,
        (UnrollInterface.unrolldt_success_iff
          (.DefT (.RecT sts') i) st start start).2 ⟨hresult, rfl⟩⟩

end properties.wasm_module_ok.ValidatedTypeUnroll
