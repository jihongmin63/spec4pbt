import properties.wasm_module_ok.ReadyMatchReachability

set_option autoImplicit false

namespace properties.wasm_module_ok.SourceReferenceLookup

theorem source_heaptype_base_or_lookup_of_subtype_success
    (c : SpecTec.context) (fin : SpecTec.final)
    (hts : List SpecTec.heaptype) (strt : SpecTec.strtype)
    (ht : SpecTec.heaptype) (start finish : Nat)
    (hsub : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_ok c (.SubT fin hts strt)⟩)
      start (.success (.of ())) finish)
    (hmem : ht ∈ ReadyMatchReachability.sourceHeaptypes strt) :
    ht ∈ HeaptypeValidation.baseHeaptypes ∨
      ∃ x : Nat, ∃ dt : SpecTec.deftype,
        c.TYPES[x]? = some dt ∧ ht = .VarHT (.StatX x) := by
  rcases ReadyMatchReachability.source_heaptype_base_or_stat_of_subtype_success
      c fin hts strt ht start finish hsub hmem with
      hbase | ⟨x, hht, hx⟩
  · exact Or.inl hbase
  · exact Or.inr ⟨x, c.TYPES[x],
      List.getElem?_eq_getElem hx, hht⟩

end properties.wasm_module_ok.SourceReferenceLookup
