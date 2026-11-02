import properties.wasm_module_ok.CandidateTypeReady

set_option autoImplicit false

namespace properties.wasm_module_ok.ReadyTypeInterfaces

open properties.wasm_module_not_ok.Rejection

theorem ready_substitution_fixed
    (c : SpecTec.context) (hready : CandidateTypeReady.Ready c)
    (p start : Nat) (dt : SpecTec.deftype)
    (_hp : p < c.TYPES.length)
    (hlookup : c.TYPES[p]? = some dt) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.deftype,
        SpecTec.SpecTecCall.«$subst_deftype» (List SpecTec.deftype)
          c.TYPES SpecTec.SpecTecCall.«$subst_of» dt⟩)
      start (.success (.of dt)) start := by
  simpa [optionOutcome, hready.substitution p dt hlookup] using
    subst_deftype_of_total dt c.TYPES start

theorem ready_unrolled_supertype_member_for_result
    (c : SpecTec.context) (hready : CandidateTypeReady.Ready c)
    (p : Nat) (dtP : SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (hp : p < c.TYPES.length)
    (hP : c.TYPES[p]? = some dtP)
    (hunroll : unrollDeftypeResult dtP = some (.SubT fin hts strt)) :
    ∀ ht ∈ hts, ∃ k : Nat, ∃ dtK : SpecTec.deftype,
      k < p ∧ c.TYPES[k]? = some dtK ∧ ht = .DefHT dtK := by
  obtain ⟨dt, fin', hts', strt', hlookup, hresult, hedges⟩ :=
    hready.unrolledPredecessors p hp
  have hdt : dt = dtP := Option.some.inj (hlookup.symm.trans hP)
  subst dt
  have hsub : SpecTec.subtype.SubT fin' hts' strt' =
      .SubT fin hts strt := Option.some.inj (hresult.symm.trans hunroll)
  have hhts : hts' = hts := by
    injection hsub with _ h _
  subst hts'
  intro ht hmem
  obtain ⟨j, hget⟩ := List.mem_iff_getElem?.mp hmem
  have hj : j < hts.length :=
    (List.getElem?_eq_some_iff.mp hget).choose
  obtain ⟨k, dtK, hkp, hlookupK, hgetK⟩ := hedges j hj
  have hht : ht = .DefHT dtK :=
    Option.some.inj (hget.symm.trans hgetK)
  exact ⟨k, dtK, hkp, hlookupK, hht⟩

end properties.wasm_module_ok.ReadyTypeInterfaces
