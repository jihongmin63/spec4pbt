import properties.wasm_module_ok.SubtypeWrapperShape
import properties.wasm_module_ok.RectypeRangeValidation
import properties.wasm_module_ok.RangeZipPosition

set_option autoImplicit false

namespace properties.wasm_module_ok.RectypeAllStatic

theorem rectype_sub_iter_all_static
    (c : SpecTec.context) (x : SpecTec.idx)
    (ns : List SpecTec.n) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Rectype_ok:rule:iter:6» c x ns sts⟩)
      start (.success (.of ())) finish) :
    ∀ n fin hts strt,
      (n, SpecTec.subtype.SubT fin hts strt) ∈ List.zip ns sts →
      ∀ ht ∈ hts,
        ∃ y : SpecTec.typeidx,
          ht = .VarHT (.StatX y) ∧ y < x + n := by
  induction ns generalizing sts start finish with
  | nil =>
      intro n fin hts strt hpair
      cases sts <;> cases hpair
  | cons n₀ ns ih =>
      cases sts with
      | nil =>
          intro n fin hts strt hpair
          cases hpair
      | cons st₀ sts =>
          cases h with
          | call hbody =>
            change SpecTecExecution.Eval SpecTec.Body
              (SpecTecExecution.tryClauses
                (SpecTec.«Rectype_ok:rule:iter:6_clauses»
                  c x (n₀ :: ns) (st₀ :: sts)))
              start (.success (.of ())) finish at hbody
            obtain ⟨idx, hselected⟩ :=
              (SpecTecExecution.tryClauses_success_iff
                (SpecTec.«Rectype_ok:rule:iter:6_clauses»
                  c x (n₀ :: ns) (st₀ :: sts))
                start (.of ()) finish).1 hbody
            unfold SpecTec.«Rectype_ok:rule:iter:6_clauses» at hselected
            cases hselected with
            | here h0 =>
                unfold SpecTec.«Rectype_ok:rule:iter:6:clause:0» at h0
                cases h0
            | next _ hrest =>
                cases hrest with
                | here h1 =>
                    unfold SpecTec.«Rectype_ok:rule:iter:6:clause:1» at h1
                    cases h1 with
                    | bind_success hhead htailplan =>
                        cases htailplan with
                        | bind_success htail _ =>
                            intro n fin hts strt hpair ht hmem
                            rcases List.mem_cons.mp hpair with heq | htailpair
                            · cases st₀
                              cases Prod.mk.inj heq with
                              | intro hn hst =>
                                  cases hn
                                  cases hst
                                  exact properties.wasm_module_ok.SubtypeWrapperShape.subtype_subtype_all_static
                                    c (x + n₀) fin hts strt _ _ hhead ht hmem
                            · exact ih _ _ _ htail n fin hts strt htailpair ht hmem
                | next _ hrest => cases hrest

theorem rectype_ok_source_all_static
    (c c' : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish i : Nat) (fin : SpecTec.final)
    (hts : List SpecTec.heaptype) (strt : SpecTec.strtype)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of c')) finish)
    (hi : i < sts.length)
    (hsource : sts[i]? = some (.SubT fin hts strt)) :
    ∀ ht ∈ hts,
      ∃ y : SpecTec.typeidx,
        ht = .VarHT (.StatX y) ∧ y < c.TYPES.length + i := by
  obtain ⟨dts, hc, before, after, hiter⟩ :=
    properties.wasm_module_ok.MatchHeaptypeBasic.rectype_ok_extract_range_and_sub_iter
      c c' sts start finish h
  have hpair :=
    properties.wasm_module_ok.RangeZipPosition.range_zip_source_position
      sts i (.SubT fin hts strt) hi hsource
  exact rectype_sub_iter_all_static
    {c with TYPES := c.TYPES ++ dts} c.TYPES.length
    (List.range sts.length) sts before after hiter
    i fin hts strt hpair

end properties.wasm_module_ok.RectypeAllStatic
