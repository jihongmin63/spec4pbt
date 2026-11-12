import properties.wasm_module_ok.UnrolledReferenceCases
import properties.wasm_module_ok.ValidatedTypeLookup

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedNestedReferences

open properties.wasm_module_not_ok.Rejection

theorem validated_type_unrolled_nested_references
    (c : SpecTec.context) (p : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length) :
    ∃ dt : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ htsU : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
      c.TYPES[p]? = some dt ∧
      unrollDeftypeResult dt = some (.SubT fin htsU strtU) ∧
      ∀ ht, ht ∈ ReadyMatchReachability.sourceHeaptypes strtU →
        ht ∈ HeaptypeValidation.baseHeaptypes ∨
        ∃ k : Nat, ∃ dtK : SpecTec.deftype,
          c.TYPES[k]? = some dtK ∧ ht = .DefHT dtK := by
  obtain ⟨before, after, sts, start, finish, i, tail,
    fin, hts, strt, dts, sts', _hbefore, hrect, _hpos,
    hi, hsource, hafter, hdts, _hafterLookup, hprefix,
    hcLookup⟩ :=
    ValidatedTypeLookup.validated_types_position_lookup c p hc hp
  obtain ⟨hts', strt', hstored, hcases⟩ :=
    UnrolledReferenceCases.rectype_ok_unrolled_structural_reference_cases
      before after c sts sts' start finish i dts tail fin hts strt
      hrect hi hsource hafter hdts hprefix
  exact ⟨.DefT (.RecT sts') i, fin,
    unrollHeaptypes hts' (.RecT sts'),
    unrollStrtype strt' (.RecT sts'),
    hcLookup,
    UnrollPositionBridge.unroll_deftype_at
      sts' i fin hts' strt' hstored,
    hcases⟩

theorem validated_type_unrolled_nested_searchable
    (c : SpecTec.context) (p : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length) :
    ∃ dt : SpecTec.deftype,
    ∃ fin : SpecTec.final,
    ∃ htsU : List SpecTec.heaptype,
    ∃ strtU : SpecTec.strtype,
      c.TYPES[p]? = some dt ∧
      unrollDeftypeResult dt = some (.SubT fin htsU strtU) ∧
      ∀ ht, ht ∈ ReadyMatchReachability.sourceHeaptypes strtU →
        ht ∈ HeaptypeValidation.baseHeaptypes ∨
        ∃ dtK : SpecTec.deftype,
        ∃ k : Nat,
          ReadyMatchHeaptypeIndex.indexOfDeftype c.TYPES dtK = some k ∧
          ht = .DefHT dtK := by
  obtain ⟨dt, fin, htsU, strtU, hlookup, hunroll, hcases⟩ :=
    validated_type_unrolled_nested_references c p hc hp
  refine ⟨dt, fin, htsU, strtU, hlookup, hunroll, ?_⟩
  intro ht hmem
  rcases hcases ht hmem with hbase | ⟨k, dtK, hget, hht⟩
  · exact Or.inl hbase
  · obtain ⟨first, hfound⟩ :=
      ReadyMatchHeaptypeIndex.indexOfDeftype_complete c.TYPES dtK
        (List.mem_iff_getElem?.mpr ⟨k, hget⟩)
    exact Or.inr ⟨dtK, first, hfound, hht⟩

end properties.wasm_module_ok.ValidatedNestedReferences
