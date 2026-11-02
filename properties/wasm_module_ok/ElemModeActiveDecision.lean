import properties.wasm_module_ok.ElemModeBaseDecision
import properties.wasm_module_ok.AddrNumtypeDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.ElemModeActiveDecision

def activeValid (c : SpecTec.context) (rt : SpecTec.reftype)
    (a : SpecTec.active) : Bool :=
  match c.TABLES[a.INDEX]? with
  | none => false
  | some (.TableT addr _ tableRt) =>
      CandidateReftypeMatch.candidateReftypeMatch c rt tableRt &&
        ConstExpressionDecision.constantExpressionResult c
          (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr)) a.OFFSET

theorem active_valid_parts
    (c : SpecTec.context) (rt : SpecTec.reftype)
    (a : SpecTec.active) :
    activeValid c rt a = true ↔
      ∃ (addr : SpecTec.addrtype) (lim : SpecTec.limits)
        (tableRt : SpecTec.reftype),
        c.TABLES[a.INDEX]? = some (.TableT addr lim tableRt) ∧
        CandidateReftypeMatch.candidateReftypeMatch c rt tableRt = true ∧
        ConstExpressionDecision.constantExpressionResult c
          (.NumT (AddrNumtypeDecision.numtypeOfAddrtype addr))
          a.OFFSET = true := by
  cases hlookup : c.TABLES[a.INDEX]? with
  | none => simp [activeValid, hlookup]
  | some tt =>
    cases tt with
    | TableT addr lim tableRt =>
      simp only [activeValid, hlookup, Bool.and_eq_true]
      constructor
      · intro hparts
        exact ⟨addr, lim, tableRt, rfl, hparts.1, hparts.2⟩
      · rintro ⟨addr', lim', tableRt', hget, hmatch, hconst⟩
        have heq := Option.some.inj hget
        cases heq
        exact ⟨hmatch, hconst⟩

theorem active_valid_index_bound
    (c : SpecTec.context) (rt : SpecTec.reftype)
    (a : SpecTec.active) (hvalid : activeValid c rt a = true) :
    a.INDEX < c.TABLES.length := by
  obtain ⟨addr, lim, tableRt, hlookup, _, _⟩ :=
    (active_valid_parts c rt a).1 hvalid
  exact (List.getElem?_eq_some_iff.mp hlookup).1

end properties.wasm_module_ok.ElemModeActiveDecision
