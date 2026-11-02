import properties.wasm_module_ok.SubstRolledReferenceCases
import properties.wasm_module_ok.ValidatedGroupUniform

set_option autoImplicit false

namespace properties.wasm_module_ok.UnrolledReferenceCases

open properties.wasm_module_not_ok.Rejection

theorem unroll_base_heaptype
    (ht : SpecTec.heaptype) (rect : SpecTec.rectype)
    (hbase : ht ∈ HeaptypeValidation.baseHeaptypes) :
    unrollHeaptype ht rect = ht := by
  cases ht <;> simp_all [HeaptypeValidation.baseHeaptypes, unrollHeaptype]

theorem unroll_reference_cases
    (pref full : List SpecTec.deftype)
    (sts' : List SpecTec.subtype) (count : Nat)
    (hprefix : ∀ x, x < pref.length → full[x]? = pref[x]?)
    (hgroup : ∀ j, j < count →
      full[pref.length + j]? = some (.DefT (.RecT sts') j))
    (raw : SpecTec.heaptype)
    (hcases :
      raw ∈ HeaptypeValidation.baseHeaptypes ∨
      (∃ x : Nat, ∃ dt : SpecTec.deftype,
        x < pref.length ∧ pref[x]? = some dt ∧ raw = .DefHT dt) ∨
      (∃ j : Nat, j < count ∧ raw = .VarHT (.RecX j))) :
    unrollHeaptype raw (.RecT sts') ∈
      HeaptypeValidation.baseHeaptypes ∨
    ∃ k : Nat, ∃ dt : SpecTec.deftype,
      full[k]? = some dt ∧
      unrollHeaptype raw (.RecT sts') = .DefHT dt := by
  rcases hcases with hbase | ⟨x, dt, hx, hget, hraw⟩ | ⟨j, hj, hraw⟩
  · left
    simpa [unroll_base_heaptype raw (.RecT sts') hbase] using hbase
  · right
    subst raw
    exact ⟨x, dt, (hprefix x hx).trans hget, rfl⟩
  · right
    subst raw
    exact ⟨pref.length + j, .DefT (.RecT sts') j,
      hgroup j hj, rfl⟩

theorem rectype_ok_group_lookup_all
    (before after c : SpecTec.context)
    (sts sts' : List SpecTec.subtype)
    (start finish i : Nat)
    (dts tail : List SpecTec.deftype)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hafter : after = {before with TYPES := before.TYPES ++ dts})
    (hdts : dts[i]? = some (.DefT (.RecT sts') i))
    (hprefix : c.TYPES = after.TYPES ++ tail) :
    ∀ j, j < sts.length →
      c.TYPES[before.TYPES.length + j]? =
        some (.DefT (.RecT sts') j) := by
  obtain ⟨uniform, _, hgroup⟩ :=
    ValidatedGroupUniform.rectype_ok_uniform_in_extension
      before after c sts start finish tail hrect hprefix
  have hiDts : i < dts.length :=
    (List.getElem?_eq_some_iff.mp hdts).choose
  have hiAfter : before.TYPES.length + i < after.TYPES.length := by
    rw [hafter, List.length_append]
    omega
  have hcurrent : c.TYPES[before.TYPES.length + i]? =
      some (.DefT (.RecT sts') i) := by
    rw [hprefix, List.getElem?_append_left hiAfter, hafter]
    rw [List.getElem?_append_right (by omega)]
    have hidx : before.TYPES.length + i - before.TYPES.length = i := by
      omega
    rw [hidx]
    exact hdts
  have hdef : SpecTec.deftype.DefT (.RecT uniform) i =
      .DefT (.RecT sts') i :=
    Option.some.inj ((hgroup i hi).symm.trans hcurrent)
  have hsame : uniform = sts' := by
    cases hdef
    rfl
  subst uniform
  exact hgroup

theorem rectype_prefix_lookup
    (before after c : SpecTec.context)
    (dts tail : List SpecTec.deftype)
    (hafter : after = {before with TYPES := before.TYPES ++ dts})
    (hprefix : c.TYPES = after.TYPES ++ tail) :
    ∀ x, x < before.TYPES.length →
      c.TYPES[x]? = before.TYPES[x]? := by
  intro x hx
  have hxAfter : x < after.TYPES.length := by
    rw [hafter, List.length_append]
    omega
  rw [hprefix, List.getElem?_append_left hxAfter, hafter,
    List.getElem?_append_left hx]

theorem rectype_ok_unrolled_reference_cases
    (before after c : SpecTec.context)
    (sts sts' : List SpecTec.subtype)
    (start finish i : Nat)
    (dts tail : List SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hafter : after = {before with TYPES := before.TYPES ++ dts})
    (hdts : dts[i]? = some (.DefT (.RecT sts') i))
    (hprefix : c.TYPES = after.TYPES ++ tail) :
    ∃ hts' : List SpecTec.heaptype,
    ∃ strt' : SpecTec.strtype,
      sts'[i]? = some (.SubT fin hts' strt') ∧
      ∀ raw, raw ∈ ReadyMatchReachability.sourceHeaptypes strt' →
        unrollHeaptype raw (.RecT sts') ∈
          HeaptypeValidation.baseHeaptypes ∨
        ∃ k : Nat, ∃ dtK : SpecTec.deftype,
          c.TYPES[k]? = some dtK ∧
          unrollHeaptype raw (.RecT sts') = .DefHT dtK := by
  obtain ⟨hts', strt', hstored, hcases⟩ :=
    SubstRolledReferenceCases.rectype_ok_appended_reference_cases
      before after sts sts' start finish i dts fin hts strt
      hrect hi hsource hafter hdts
  refine ⟨hts', strt', hstored, ?_⟩
  intro raw hmem
  exact unroll_reference_cases before.TYPES c.TYPES sts' sts.length
    (rectype_prefix_lookup before after c dts tail hafter hprefix)
    (rectype_ok_group_lookup_all before after c sts sts'
      start finish i dts tail hrect hi hafter hdts hprefix)
    raw (hcases raw hmem)

theorem rectype_ok_unrolled_structural_reference_cases
    (before after c : SpecTec.context)
    (sts sts' : List SpecTec.subtype)
    (start finish i : Nat)
    (dts tail : List SpecTec.deftype)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype)
    (hrect : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hafter : after = {before with TYPES := before.TYPES ++ dts})
    (hdts : dts[i]? = some (.DefT (.RecT sts') i))
    (hprefix : c.TYPES = after.TYPES ++ tail) :
    ∃ hts' : List SpecTec.heaptype,
    ∃ strt' : SpecTec.strtype,
      sts'[i]? = some (.SubT fin hts' strt') ∧
      ∀ ht, ht ∈ ReadyMatchReachability.sourceHeaptypes
          (unrollStrtype strt' (.RecT sts')) →
        ht ∈ HeaptypeValidation.baseHeaptypes ∨
        ∃ k : Nat, ∃ dtK : SpecTec.deftype,
          c.TYPES[k]? = some dtK ∧ ht = .DefHT dtK := by
  obtain ⟨hts', strt', hstored, hrawCases⟩ :=
    rectype_ok_unrolled_reference_cases before after c sts sts'
      start finish i dts tail fin hts strt
      hrect hi hsource hafter hdts hprefix
  refine ⟨hts', strt', hstored, ?_⟩
  intro ht hmem
  obtain ⟨raw, hrawMem, hresult⟩ :=
    (ReadyMatchReachability.source_heaptype_mem_unroll_iff
      strt' (.RecT sts') ht).mp hmem
  subst ht
  exact hrawCases raw hrawMem

end properties.wasm_module_ok.UnrolledReferenceCases
