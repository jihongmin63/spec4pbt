import properties.wasm_module_ok.RectypeSourceValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.RollSourceClassification

open properties.wasm_module_not_ok.Rejection

theorem roll_static_in_group_interval
    (base count x : Nat) (hbound : x < base + count) :
    (x < base ∧
      rollHeaptype (.VarHT (.StatX x)) base (base + count) =
        .VarHT (.StatX x)) ∨
    (∃ j, x = base + j ∧ j < count ∧
      rollHeaptype (.VarHT (.StatX x)) base (base + count) =
        .VarHT (.RecX j)) := by
  by_cases hearly : x < base
  · left
    refine ⟨hearly, ?_⟩
    simp [rollHeaptype, rollTypevar, show ¬ base ≤ x by omega]
  · right
    let j := x - base
    have hbase : base ≤ x := by omega
    have hx : x = base + j := by omega
    have hj : j < count := by omega
    refine ⟨j, hx, hj, ?_⟩
    simp [rollHeaptype, rollTypevar, hbase, hbound, j]

theorem roll_base_heaptype
    (ht : SpecTec.heaptype) (base count : Nat)
    (hbase : ht ∈ HeaptypeValidation.baseHeaptypes) :
    rollHeaptype ht base (base + count) = ht := by
  cases ht <;> simp_all [HeaptypeValidation.baseHeaptypes, rollHeaptype]

theorem rectype_ok_source_reference_roll_cases
    (before after : SpecTec.context)
    (sts : List SpecTec.subtype)
    (start finish i : Nat)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (ht : SpecTec.heaptype)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok before (.RecT sts)⟩)
      start (.success (.of after)) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt))
    (hmem : ht ∈ ReadyMatchReachability.sourceHeaptypes strt) :
    rollHeaptype ht before.TYPES.length
      (before.TYPES.length + sts.length) ∈
        HeaptypeValidation.baseHeaptypes ∨
    (∃ x : Nat, x < before.TYPES.length ∧
      rollHeaptype ht before.TYPES.length
        (before.TYPES.length + sts.length) =
          .VarHT (.StatX x)) ∨
    (∃ j : Nat, j < sts.length ∧
      rollHeaptype ht before.TYPES.length
        (before.TYPES.length + sts.length) =
          .VarHT (.RecX j)) := by
  rcases RectypeSourceValidation.rectype_ok_source_heaptype_base_or_stat
      before after sts start finish i fin hts strt ht
      hrect hi hsource hmem with hbase | ⟨x, hht, hx⟩
  · left
    simpa [roll_base_heaptype ht before.TYPES.length sts.length hbase] using hbase
  · subst ht
    have hlength := RectypeSourceValidation.rectype_ok_types_length
      before after sts start finish hrect
    have hbound : x < before.TYPES.length + sts.length := by
      simpa [hlength] using hx
    rcases roll_static_in_group_interval
      before.TYPES.length sts.length x hbound with
      ⟨hearly, hroll⟩ | ⟨j, _, hj, hroll⟩
    · exact Or.inr (Or.inl ⟨x, hearly, hroll⟩)
    · exact Or.inr (Or.inr ⟨j, hj, hroll⟩)

end properties.wasm_module_ok.RollSourceClassification
