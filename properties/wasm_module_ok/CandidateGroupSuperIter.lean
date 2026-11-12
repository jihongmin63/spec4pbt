import properties.wasm_module_ok.CandidateStaticSuperList
import properties.wasm_module_ok.CandidateSourceChecks
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateGroupSuperIter

theorem iter6_nil_success (c : SpecTec.context)
    (base n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Rectype_ok:rule:iter:6» c base [] []⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«Rectype_ok:rule:iter:6_clauses» c base [] []))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_success
  exact SpecTecExecution.Eval.pure ()

theorem iter6_cons_success_iff
    (c : SpecTec.context) (base i : Nat)
    (is : List Nat) (st : SpecTec.subtype)
    (sts : List SpecTec.subtype) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Rectype_ok:rule:iter:6»
          c base (i :: is) (st :: sts)⟩)
      n (.success (.of ())) finish ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit,
          SpecTec.Call.Subtype_sub_ok c (base + i) st⟩)
        n (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit,
          SpecTec.Call.«Rectype_ok:rule:iter:6»
            c base is sts⟩)
        middle (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (properties.wasm_module_ok.Execution.tryClauses_success_iff
          (SpecTec.«Rectype_ok:rule:iter:6_clauses»
            c base (i :: is) (st :: sts))
          n (.of ()) finish).1 hbody
      unfold SpecTec.«Rectype_ok:rule:iter:6_clauses» at hselected
      cases hselected with
      | here hfirst =>
          unfold SpecTec.«Rectype_ok:rule:iter:6:clause:0» at hfirst
          cases hfirst
      | next _ hrest =>
          cases hrest with
          | here hsecond =>
              unfold SpecTec.«Rectype_ok:rule:iter:6:clause:1» at hsecond
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
        (SpecTec.«Rectype_ok:rule:iter:6_clauses»
          c base (i :: is) (st :: sts)))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.tryClauses_cons_success
      unfold SpecTec.«Rectype_ok:rule:iter:6:clause:1»
      apply SpecTecExecution.Eval.bind_success hhead
      apply SpecTecExecution.Eval.bind_success hrest
      exact SpecTecExecution.Eval.pure ()

end properties.wasm_module_ok.CandidateGroupSuperIter
