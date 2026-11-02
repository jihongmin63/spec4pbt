import properties.wasm_module_ok.RollSourceClassification

set_option autoImplicit false

namespace properties.wasm_module_ok.SubstRolledReferenceCases

open properties.wasm_module_not_ok.Rejection

theorem subst_rolled_reference_cases
    (pref : List SpecTec.deftype) (count : Nat)
    (rolled raw : SpecTec.heaptype)
    (hcases :
      rolled ∈ HeaptypeValidation.baseHeaptypes ∨
      (∃ x : Nat, x < pref.length ∧ rolled = .VarHT (.StatX x)) ∨
      (∃ j : Nat, j < count ∧ rolled = .VarHT (.RecX j)))
    (hsubst : substHeaptypeResult rolled pref = some raw) :
    raw ∈ HeaptypeValidation.baseHeaptypes ∨
    (∃ x : Nat, ∃ dt : SpecTec.deftype,
      x < pref.length ∧ pref[x]? = some dt ∧ raw = .DefHT dt) ∨
    (∃ j : Nat, j < count ∧ raw = .VarHT (.RecX j)) := by
  rcases hcases with hbase | ⟨x, hx, hrolled⟩ | ⟨j, hj, hrolled⟩
  · have hfixed : substHeaptypeResult rolled pref = some rolled := by
      cases rolled <;>
        simp_all [HeaptypeValidation.baseHeaptypes, substHeaptypeResult]
    rw [hfixed] at hsubst
    cases hsubst
    exact Or.inl hbase
  · subst rolled
    obtain ⟨dt, hget⟩ : ∃ dt, pref[x]? = some dt :=
      ⟨pref[x], List.getElem?_eq_getElem hx⟩
    simp [substHeaptypeResult, substOfResult, hget] at hsubst
    subst raw
    exact Or.inr (Or.inl ⟨x, dt, hx, hget, rfl⟩)
  · subst rolled
    simp [substHeaptypeResult, substOfResult] at hsubst
    subst raw
    exact Or.inr (Or.inr ⟨j, hj, rfl⟩)

theorem rectype_ok_appended_reference_cases
    (before after : SpecTec.context)
    (sts sts' : List SpecTec.subtype)
    (start finish i : Nat)
    (dts : List SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hafter : after = {before with TYPES := before.TYPES ++ dts})
    (hdts : dts[i]? = some (.DefT (.RecT sts') i)) :
    ∃ hts' : List SpecTec.heaptype,
    ∃ strt' : SpecTec.strtype,
      sts'[i]? = some (.SubT fin hts' strt') ∧
      ∀ raw, raw ∈ ReadyMatchReachability.sourceHeaptypes strt' →
        raw ∈ HeaptypeValidation.baseHeaptypes ∨
        (∃ x : Nat, ∃ dt : SpecTec.deftype,
          x < before.TYPES.length ∧
          before.TYPES[x]? = some dt ∧ raw = .DefHT dt) ∨
        (∃ j : Nat, j < sts.length ∧ raw = .VarHT (.RecX j)) := by
  obtain ⟨hts', strt', hget, hpredecessor⟩ :=
    RollReferenceProvenance.rectype_ok_appended_source_reference
      before after sts sts' start finish i dts fin hts strt
      hrect hi hsource hafter hdts
  refine ⟨hts', strt', hget, ?_⟩
  intro raw hmem
  obtain ⟨ht, hsourceMem, hsubst⟩ := hpredecessor raw hmem
  rw [Nat.add_comm sts.length before.TYPES.length] at hsubst
  exact subst_rolled_reference_cases before.TYPES sts.length
    (rollHeaptype ht before.TYPES.length
      (before.TYPES.length + sts.length)) raw
    (RollSourceClassification.rectype_ok_source_reference_roll_cases
      before after sts start finish i fin hts strt ht
      hrect hi hsource hsourceMem)
    hsubst

end properties.wasm_module_ok.SubstRolledReferenceCases
