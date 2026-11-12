import properties.wasm_module_ok.SubstOutputDeftype
import properties.wasm_module_ok.ValidatedTypeLookup
import properties.wasm_module_ok.RectypeAppendedShape

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedTypeSubstitution

open properties.wasm_module_not_ok.Rejection

theorem validated_type_substitution_fixed
    (c : SpecTec.context) (p start : Nat) (dtP : SpecTec.deftype)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length)
    (hlookup : c.TYPES[p]? = some dtP) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.deftype,
        SpecTec.Call.«$subst_deftype» (List SpecTec.deftype)
          c.TYPES SpecTec.Call.«$subst_of» dtP⟩)
      start (.success (.of dtP)) start := by
  obtain ⟨before, after, sts, s, f, i, tail,
      fin, hts, strt, dts, sts', _hbefore, hrect,
      _hpos, hi, _hsource, hafter, hdts,
      _hafterLookup, _hprefix, hlookup'⟩ :=
    ValidatedTypeLookup.validated_types_position_lookup c p hc hp
  obtain ⟨dts', hafter', hpositions⟩ :=
    RectypeAppendedShape.rectype_ok_appended_position_shape
      before after sts s f hrect
  obtain ⟨rect', hdts', hsubst⟩ := hpositions i hi
  have hctxEq :
      {before with TYPES := before.TYPES ++ dts'} =
        {before with TYPES := before.TYPES ++ dts} :=
    hafter'.symm.trans hafter
  have hlistEq : before.TYPES ++ dts' = before.TYPES ++ dts :=
    congrArg SpecTec.context.TYPES hctxEq
  have hdtsEq : dts' = dts := List.append_cancel_left hlistEq
  rw [hdtsEq] at hdts'
  have hdefEq :
      SpecTec.deftype.DefT rect' i = .DefT (.RecT sts') i :=
    Option.some.inj (hdts'.symm.trans hdts)
  have hrectEq : rect' = .RecT sts' := by
    injection hdefEq with hrectEq
  rw [hrectEq] at hsubst
  have hsource : substDeftypeResult
      (.DefT (.RecT (rollSubtypes sts before.TYPES.length
        (sts.length + before.TYPES.length))) i)
      before.TYPES = some (.DefT (.RecT sts') i) := by
    simp [substDeftypeResult, hsubst]
  have hfixed :
      substDeftypeResult (.DefT (.RecT sts') i) c.TYPES =
        some (.DefT (.RecT sts') i) :=
    SubstOutputDeftype.substDeftypeResult_output_fixed
      _ before.TYPES c.TYPES _ hsource
  have hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.deftype,
        SpecTec.Call.«$subst_deftype» (List SpecTec.deftype)
          c.TYPES SpecTec.Call.«$subst_of»
            (SpecTec.deftype.DefT (.RecT sts') i)⟩)
      start (.success (.of (SpecTec.deftype.DefT (.RecT sts') i))) start := by
    simpa [optionOutcome, hfixed] using
      subst_deftype_of_total (.DefT (.RecT sts') i) c.TYPES start
  have hdtEq : SpecTec.deftype.DefT (.RecT sts') i = dtP :=
    Option.some.inj (hlookup'.symm.trans hlookup)
  subst dtP
  exact hcall

theorem validated_type_substitution_total
    (c : SpecTec.context) (p start : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length) :
    ∃ dtP sP : SpecTec.deftype,
      c.TYPES[p]? = some dtP ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.deftype,
          SpecTec.Call.«$subst_deftype» (List SpecTec.deftype)
            c.TYPES SpecTec.Call.«$subst_of» dtP⟩)
        start (.success (.of sP)) start := by
  let dtP : SpecTec.deftype := c.TYPES[p]
  have hlookup : c.TYPES[p]? = some dtP := List.getElem?_eq_getElem hp
  exact ⟨dtP, dtP, hlookup,
    validated_type_substitution_fixed c p start dtP hc hp hlookup⟩

end properties.wasm_module_ok.ValidatedTypeSubstitution
