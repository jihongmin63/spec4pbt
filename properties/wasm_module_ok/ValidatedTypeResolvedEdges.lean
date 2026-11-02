import properties.wasm_module_ok.ValidatedTypePredecessor

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedTypeResolvedEdges

open properties.wasm_module_ok.ValidatedTypeChain

theorem validated_types_position_resolved_edges
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
              hts'[j]? = some (.DefHT dt) ∧ c.TYPES[k]? = some dt) ∨
            (∃ q : Nat, ∃ stsQ : List SpecTec.subtype,
              k = before.TYPES.length + q ∧ q < i ∧
              hts'[j]? = some (.VarHT (.RecX q)) ∧
              c.TYPES[k]? = some (.DefT (.RecT stsQ) q))) := by
  obtain ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, dts, sts', hbefore, hrect,
    hpos, hi, hsource, hafter, hdts, hprefix, hcLookup, hedges⟩ :=
    ValidatedTypeActualEdges.validated_types_position_actual_edges c p hc hp
  refine ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, dts, sts', hbefore, hrect,
    hpos, hi, hsource, hafter, hdts, hprefix, hcLookup, ?_⟩
  intro j hj
  obtain ⟨k, hts', strt', hstatic, hlt, hsts, hcase⟩ := hedges j hj
  refine ⟨k, hts', strt', hstatic, hlt, hsts, ?_⟩
  rcases hcase with ⟨dt, hk, hlookup, hht⟩ | ⟨hge, hdiff, hht⟩
  · have hpred :=
      ValidatedTypePredecessor.rectype_predecessor_lookup
        before after c sts start finish i k dts tail
        hrect hi hafter hprefix (Or.inl ⟨dt, hk, hlookup⟩)
    rcases hpred with ⟨dt', _hk', hlookup', hcLookup'⟩ |
      ⟨q, _stsQ, hkEq, _hq, _hcLookup'⟩
    · have hdt : dt' = dt := Option.some.inj (hlookup'.symm.trans hlookup)
      subst dt'
      exact Or.inl ⟨dt, hk, hlookup, hht, hcLookup'⟩
    · omega
  · have hpred :=
      ValidatedTypePredecessor.rectype_predecessor_lookup
        before after c sts start finish i k dts tail
        hrect hi hafter hprefix (Or.inr ⟨hge, hdiff⟩)
    rcases hpred with ⟨_dt, hk, _hlookup, _hcLookup⟩ |
      ⟨q, stsQ, hkEq, hq, hcLookup'⟩
    · omega
    · have hqEq : k - before.TYPES.length = q := by omega
      rw [hqEq] at hht
      exact Or.inr ⟨q, stsQ, hkEq, hq, hht, hcLookup'⟩

end properties.wasm_module_ok.ValidatedTypeResolvedEdges
