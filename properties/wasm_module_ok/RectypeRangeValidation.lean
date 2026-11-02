import properties.wasm_module_ok.MatchHeaptypeBasic
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchHeaptypeBasic

theorem rectype_ok_extract_range_and_sub_iter
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish) :
    ∃ dts : List SpecTec.deftype,
      c' = {c with TYPES := c.TYPES ++ dts} ∧
      (∃ before after : Nat,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Unit,
            SpecTec.Call.«Rectype_ok:rule:iter:6»
              {c with TYPES := c.TYPES ++ dts}
              c.TYPES.length (List.range sts.length) sts⟩)
          before (.success (.of ())) after) := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Rectype_ok_clauses c (.RecT sts)))
      start (.success (.of c')) finish at hbody
    obtain ⟨idx, hselected⟩ :=
      (properties.wasm_module_ok.Execution.tryClauses_success_iff
        (SpecTec.Rectype_ok_clauses c (.RecT sts))
        start (.of c') finish).1 hbody
    unfold SpecTec.Rectype_ok_clauses at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«Rectype_ok:clause:0» at h0
      dsimp only at h0
      cases h0 with
      | bind_success hrange h1 =>
        rename_i ns
        have hns := range_success_eq sts.length ns _ _ hrange
        subst ns
        dsimp only at h1
        cases h1 with
        | bind_success hroll h2 =>
          dsimp only at h2
          cases h2 with
          | bind_success hsubst h3 =>
            rename_i dts
            dsimp only at h3
            cases h3 with
            | bind_success hiter5 h4 =>
              dsimp only at h4
              cases h4 with
              | bind_success hguard h5 =>
                dsimp only at h5
                cases h5 with
                | bind_success hiter6 h6 =>
                  rename_i v
                  cases h6
                  cases v
                  exact ⟨dts, rfl, _, _, hiter6⟩
    | next _ hrest => cases hrest

theorem rectype_ok_range_pairs_static_lt
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish) :
    ∃ dts : List SpecTec.deftype,
      c' = {c with TYPES := c.TYPES ++ dts} ∧
      (∀ n fin hts strt,
        (n, SpecTec.subtype.SubT fin hts strt) ∈
          List.zip (List.range sts.length) sts →
        ∀ y : SpecTec.typeidx,
          .VarHT (.StatX y) ∈ hts → y < c.TYPES.length + n) := by
  obtain ⟨dts, hc, before, after, hiter⟩ :=
    rectype_ok_extract_range_and_sub_iter c c' sts start finish h
  refine ⟨dts, hc, ?_⟩
  intro n fin hts strt hpair y hy
  exact rectype_sub_iter_static_lt
    {c with TYPES := c.TYPES ++ dts} c.TYPES.length
    (List.range sts.length) sts before after hiter
    n fin hts strt hpair y hy

end properties.wasm_module_ok.MatchHeaptypeBasic
