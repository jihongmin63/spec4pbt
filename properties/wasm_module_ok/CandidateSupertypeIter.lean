import properties.wasm_module_ok.CandidateStaticMatchResult

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateSupertypeIter

theorem iter0_nil_success
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (strt : SpecTec.strtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Subtype_sub_ok:rule:iter:0» c x strt []⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» c x strt []))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_success
  exact SpecTecExecution.Eval.pure ()

theorem iter0_cons_success_iff
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (strt : SpecTec.strtype) (ht : SpecTec.heaptype)
    (hts : List SpecTec.heaptype) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Subtype_sub_ok:rule:iter:0»
          c x strt (ht :: hts)⟩)
      n (.success (.of ())) finish ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Subtype_sub_ok' c x strt ht⟩)
        n (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit,
          SpecTec.Call.«Subtype_sub_ok:rule:iter:0» c x strt hts⟩)
        middle (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.tryClauses_success_iff
          (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses»
            c x strt (ht :: hts))
          n (.of ()) finish).1 hbody
      unfold SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» at hselected
      cases hselected with
      | here hfirst =>
          unfold SpecTec.«Subtype_sub_ok:rule:iter:0:clause:0» at hfirst
          cases hfirst
      | next _ hrest =>
          cases hrest with
          | here hsecond =>
              unfold SpecTec.«Subtype_sub_ok:rule:iter:0:clause:1» at hsecond
              cases hsecond with
              | bind_success hhead htailplan =>
                  rename_i middle _
                  cases htailplan with
                  | bind_success htail hpure =>
                      cases hpure
                      exact ⟨middle, hhead, htail⟩
          | next _ hnone => cases hnone
  · rintro ⟨middle, hhead, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses»
          c x strt (ht :: hts)))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«Subtype_sub_ok:rule:iter:0:clause:1»
      apply SpecTecExecution.Eval.bind_success hhead
      apply SpecTecExecution.Eval.bind_success hrest
      exact SpecTecExecution.Eval.pure ()

theorem subtype_sub_success_iff_iter0
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Subtype_sub_ok c x (.SubT fin hts strt)⟩)
      n (.success (.of ())) finish ↔
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Subtype_sub_ok:rule:iter:0» c x strt hts⟩)
      n (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.tryClauses_success_iff
          (SpecTec.Subtype_sub_ok_clauses c x (.SubT fin hts strt))
          n (.of ()) finish).1 hbody
      unfold SpecTec.Subtype_sub_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
          unfold SpecTec.«Subtype_sub_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hiter hpure =>
              cases hpure
              exact hiter
      | next _ hnone => cases hnone
  · intro hiter
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Subtype_sub_ok_clauses c x (.SubT fin hts strt)))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_success
    unfold SpecTec.«Subtype_sub_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success hiter
    exact SpecTecExecution.Eval.pure ()

end properties.wasm_module_ok.CandidateSupertypeIter
