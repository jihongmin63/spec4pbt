import properties.wasm_module_ok.SubtypeListShape

set_option autoImplicit false

namespace properties.wasm_module_ok.SubtypeWrapperShape

theorem subtype_subtype_all_static
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_sub_ok c x
          (.SubT fin hts strt)⟩)
      start (.success (.of ())) finish) :
    ∀ ht ∈ hts,
      ∃ y : SpecTec.typeidx,
        ht = .VarHT (.StatX y) ∧ y < x := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Subtype_sub_ok_clauses c x
          (SpecTec.subtype.SubT fin hts strt)) ())
      start (.success (.of ())) finish at hbody
    obtain ⟨idx, hselected⟩ :=
      (SpecTecExecution.firstSuccess_success_iff
        (SpecTec.Subtype_sub_ok_clauses c x
          (SpecTec.subtype.SubT fin hts strt)) ()
        start (.of ()) finish).1 hbody
    unfold SpecTec.Subtype_sub_ok_clauses at hselected
    cases hselected with
    | here h0 =>
      unfold SpecTec.«Subtype_sub_ok:clause:0» at h0
      cases h0 with
      | bind_success hiter _ =>
        exact properties.wasm_module_ok.SubtypeListShape.subtype_sub_iter_all_static
          c x strt hts _ _ hiter
    | next _ hrest => cases hrest

end properties.wasm_module_ok.SubtypeWrapperShape
