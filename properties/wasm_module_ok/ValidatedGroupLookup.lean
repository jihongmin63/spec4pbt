import properties.wasm_module_ok.ValidatedGroupUniform
import properties.wasm_module_ok.ValidatedTypeLookup

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedGroupLookup

open properties.wasm_module_ok.ValidatedTypeChain

/-- A validated position identifies its whole substituted recursive group,
including all sibling definitions in the final type table. -/
theorem validated_position_uniform_group
    (c : SpecTec.context) (p : Nat)
    (hc : ValidatedTypes c) (hp : p < c.TYPES.length) :
    ∃ before after : SpecTec.context,
    ∃ sts : List SpecTec.subtype,
    ∃ start finish i : Nat,
    ∃ tail : List SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ hts : List SpecTec.heaptype,
    ∃ strt : SpecTec.strtype,
    ∃ sts' : List SpecTec.subtype,
      ValidatedTypes before ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context,
          SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
        start (.success (.of after)) finish ∧
      p = before.TYPES.length + i ∧
      i < sts.length ∧
      sts[i]? = some (.SubT fin hts strt) ∧
      c.TYPES = after.TYPES ++ tail ∧
      c.TYPES[p]? = some (.DefT (.RecT sts') i) ∧
      sts'.length = sts.length ∧
      ∀ j, j < sts.length →
        c.TYPES[before.TYPES.length + j]? =
          some (.DefT (.RecT sts') j) := by
  obtain ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, dts, sts', hbefore, hrect, hpos,
    hi, hsource, _hafter, _hdts, _hafterLookup,
    hprefix, hlookup⟩ :=
    ValidatedTypeLookup.validated_types_position_lookup c p hc hp
  obtain ⟨uniform, hlen, huniform⟩ :=
    ValidatedGroupUniform.rectype_ok_uniform_in_extension
      before after c sts start finish tail hrect hprefix
  have huniP : c.TYPES[p]? = some (.DefT (.RecT uniform) i) := by
    simpa only [hpos] using huniform i hi
  have hdef : SpecTec.deftype.DefT (.RecT uniform) i =
      .DefT (.RecT sts') i :=
    Option.some.inj (huniP.symm.trans hlookup)
  have hsts : uniform = sts' := by
    cases hdef
    rfl
  subst uniform
  exact ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, sts', hbefore, hrect, hpos,
    hi, hsource, hprefix, hlookup, hlen, huniform⟩

end properties.wasm_module_ok.ValidatedGroupLookup
