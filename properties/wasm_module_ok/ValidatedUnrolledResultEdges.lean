import properties.wasm_module_ok.ValidatedUnrolledPredecessors

set_option autoImplicit false

namespace properties.wasm_module_ok.ValidatedUnrolledResultEdges

theorem validated_unrolled_supertype_member_for_result
    (c : SpecTec.context) (p : Nat)
    (dtP : SpecTec.deftype) (fin : SpecTec.final)
    (hts : List SpecTec.heaptype) (strt : SpecTec.strtype)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hp : p < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hunroll : properties.wasm_module_not_ok.Rejection.unrollDeftypeResult dtP =
      some (.SubT fin hts strt)) :
    ∀ ht ∈ hts, ∃ k : Nat, ∃ dtK : SpecTec.deftype,
      k < p ∧ c.TYPES[k]? = some dtK ∧ ht = .DefHT dtK := by
  obtain ⟨dt, fin', hts', strt', hlookup, hresult, hedges⟩ :=
    ValidatedUnrolledPredecessors.validated_type_unrolled_supertype_member
      c p hc hp
  have hdt : dt = dtP := Option.some.inj (hlookup.symm.trans hP)
  subst dt
  have hsub : SpecTec.subtype.SubT fin' hts' strt' =
      .SubT fin hts strt := Option.some.inj (hresult.symm.trans hunroll)
  have hhts : hts' = hts := by
    injection hsub with _ h _
  subst hts'
  exact hedges

end properties.wasm_module_ok.ValidatedUnrolledResultEdges
