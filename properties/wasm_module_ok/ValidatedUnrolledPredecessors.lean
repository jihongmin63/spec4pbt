import properties.wasm_module_ok.RectypeTransformedSubtype
import properties.wasm_module_ok.ValidatedTypeResolvedEdges
import properties.wasm_module_ok.UnrollPositionBridge

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedUnrolledPredecessors

open properties.wasm_module_ok.ValidatedTypeChain
open properties.wasm_module_not_ok.Rejection

theorem validated_type_unrolled_predecessors
    (c : SpecTec.context) (p : Nat)
    (hc : ValidatedTypes c)
    (hp : p < c.TYPES.length) :
    ∃ dt : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ htsU : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
      c.TYPES[p]? = some dt ∧
      unrollDeftypeResult dt = some (.SubT fin htsU strtU) ∧
      ∀ j, j < htsU.length →
        ∃ k : Nat, ∃ dtK : SpecTec.deftype,
          k < p ∧ c.TYPES[k]? = some dtK ∧
          htsU[j]? = some (.DefHT dtK) := by
  obtain ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, dts, sts', _hbefore, hrect,
    _hpos, hi, hsource, hafter, hdts, hprefix, hcLookup, hedges⟩ :=
    ValidatedTypeResolvedEdges.validated_types_position_resolved_edges c p hc hp
  obtain ⟨htsT, strtT, htrans, hlen⟩ :=
    RectypeTransformedSubtype.rectype_ok_appended_transformed_subtype
      before after sts sts' start finish i dts fin hts strt
      hrect hi hsource hafter hdts
  refine ⟨.DefT (.RecT sts') i, fin,
    unrollHeaptypes htsT (.RecT sts'),
    unrollStrtype strtT (.RecT sts'),
    hcLookup,
    UnrollPositionBridge.unroll_deftype_at sts' i fin htsT strtT htrans,
    ?_⟩
  intro j hjU
  have hjT : j < htsT.length := by
    simpa [unrollHeaptypes] using hjU
  have hj : j < hts.length := by omega
  obtain ⟨k, htsE, strtE, _hstatic, hkp, htransE, hcase⟩ :=
    hedges j hj
  have hsubEq :
      SpecTec.subtype.SubT fin htsE strtE = .SubT fin htsT strtT :=
    Option.some.inj (htransE.symm.trans htrans)
  have htsEq : htsE = htsT := by
    injection hsubEq with _ h _
  rw [htsEq] at hcase
  rcases hcase with ⟨dt, _hk, _hbeforeLookup, hht, hcPred⟩ |
    ⟨q, _stsQ, hkEq, hq, hht, _hcPred⟩
  · have hu :=
      UnrollPositionBridge.unroll_heaptypes_at
        htsT (.RecT sts') j (.DefHT dt) hht
    simp [unrollHeaptype] at hu
    exact ⟨k, dt, hkp, hcPred, hu⟩
  · have hcSame :=
      RectypeLocalLookup.rectype_ok_local_same_group_lookup
        before after c sts sts' start finish i q dts tail
        hrect hi hq hafter hdts hprefix
    have hu :=
      UnrollPositionBridge.unroll_heaptypes_at
        htsT (.RecT sts') j (.VarHT (.RecX q)) hht
    simp [unrollHeaptype, unrollTypevar] at hu
    refine ⟨k, .DefT (.RecT sts') q, hkp, ?_, hu⟩
    rw [hkEq]
    exact hcSame

theorem validated_type_unrolldt_predecessors
    (c : SpecTec.context) (p start : Nat)
    (hc : ValidatedTypes c)
    (hp : p < c.TYPES.length) :
    ∃ dt : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ htsU : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
      c.TYPES[p]? = some dt ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dt⟩)
        start (.success (.of (SpecTec.subtype.SubT fin htsU strtU))) start ∧
      ∀ j, j < htsU.length →
        ∃ k : Nat, ∃ dtK : SpecTec.deftype,
          k < p ∧ c.TYPES[k]? = some dtK ∧
          htsU[j]? = some (.DefHT dtK) := by
  obtain ⟨dt, fin, htsU, strtU, hlookup, hresult, hedges⟩ :=
    validated_type_unrolled_predecessors c p hc hp
  exact ⟨dt, fin, htsU, strtU, hlookup,
    (UnrollInterface.unrolldt_success_iff
      dt (.SubT fin htsU strtU) start start).2 ⟨hresult, rfl⟩,
    hedges⟩

theorem validated_type_unrolled_supertype_member
    (c : SpecTec.context) (p : Nat)
    (hc : ValidatedTypes c)
    (hp : p < c.TYPES.length) :
    ∃ dt : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ htsU : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
      c.TYPES[p]? = some dt ∧
      unrollDeftypeResult dt = some (.SubT fin htsU strtU) ∧
      ∀ ht, ht ∈ htsU →
        ∃ k : Nat, ∃ dtK : SpecTec.deftype,
          k < p ∧ c.TYPES[k]? = some dtK ∧
          ht = .DefHT dtK := by
  obtain ⟨dt, fin, htsU, strtU, hlookup, hresult, hedges⟩ :=
    validated_type_unrolled_predecessors c p hc hp
  refine ⟨dt, fin, htsU, strtU, hlookup, hresult, ?_⟩
  intro ht hmem
  obtain ⟨j, hget⟩ := List.mem_iff_getElem?.mp hmem
  have hj : j < htsU.length :=
    (List.getElem?_eq_some_iff.mp hget).choose
  obtain ⟨k, dtK, hkp, hcPred, hgetK⟩ := hedges j hj
  have heq : ht = .DefHT dtK :=
    Option.some.inj (hget.symm.trans hgetK)
  exact ⟨k, dtK, hkp, hcPred, heq⟩

end properties.wasm_module_ok.ValidatedUnrolledPredecessors
