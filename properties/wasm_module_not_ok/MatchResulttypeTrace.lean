import properties.wasm_module_not_ok.MatchFunctypeTrace

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_resulttype_iter_nil_success
    (d : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0» d [] []⟩)
      start (.success (.of ())) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_resulttype:case_1:iter:0_clauses» d [] []) ())
    start (.success (.of ())) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_resulttype:case_1:iter:0:clause:0» d [] [])
    start (.success (.of ())) start
  exact SpecTecExecution.Eval.pure ()

theorem match_resulttype_iter_cons_success
    (d : List SpecTec.deftype) (a b : SpecTec.valtype)
    (as bs : List SpecTec.valtype)
    (start middle finalSupply : Nat)
    (hhead : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» d a b⟩)
      start (.success (.of true)) middle)
    (htail : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0» d as bs⟩)
      middle (.success (.of ())) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0»
          d (a :: as) (b :: bs)⟩)
      start (.success (.of ())) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_resulttype:case_1:iter:0_clauses»
        d (a :: as) (b :: bs)) ())
    start (.success (.of ())) finalSupply
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_resulttype:case_1:iter:0:clause:0»
        d (a :: as) (b :: bs)) start .unmatch start
    exact SpecTecExecution.Eval.unmatch
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
        d (a :: as) (b :: bs))
      start (.success (.of ())) finalSupply
    unfold SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
    apply SpecTecExecution.Eval.bind_success hhead
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success htail
      exact SpecTecExecution.Eval.pure ()

theorem match_resulttype_iter_cons_success_iff
    (d : List SpecTec.deftype) (a b : SpecTec.valtype)
    (as bs : List SpecTec.valtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0»
          d (a :: as) (b :: bs)⟩)
      start (.success (.of ())) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» d a b⟩)
        start (.success (.of true)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0» d as bs⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_resulttype:case_1:iter:0:clause:0»
            d (a :: as) (b :: bs))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
              d (a :: as) (b :: bs)] ()))
        start (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          change SpecTecExecution.Eval SpecTec.specTecProgram .unmatch
            start (.success (.of ())) finalSupply at hfirst
          cases hfirst
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
                d (a :: as) (b :: bs))
              (fun _ => .unmatch))
            start (.success (.of ())) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
              unfold SpecTec.«$match_resulttype:case_1:iter:0:clause:1» at hsecond
              cases hsecond with
              | bind_success hhead hrest =>
                  cases hrest with
                  | bind_success hguard hrest =>
                      cases hguard with
                      | guard_true htrue =>
                          cases htrue
                          cases hrest with
                          | bind_success htail hpure =>
                              cases hpure with
                              | pure => exact ⟨_, hhead, htail⟩
          | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨middle, hhead, htail⟩
    exact match_resulttype_iter_cons_success d a b as bs
      start middle finalSupply hhead htail

theorem match_resulttype_iter_left_empty_unmatch
    (d : List SpecTec.deftype) (b : SpecTec.valtype)
    (bs : List SpecTec.valtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0»
          d [] (b :: bs)⟩)
      start .unmatch start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_resulttype:case_1:iter:0_clauses»
        d [] (b :: bs)) ())
    start .unmatch start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_resulttype:case_1:iter:0:clause:0»
        d [] (b :: bs)) start .unmatch start
    exact SpecTecExecution.Eval.unmatch
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
          d [] (b :: bs)) start .unmatch start
      exact SpecTecExecution.Eval.unmatch
    · exact SpecTecExecution.firstSuccess_nil () start

theorem match_resulttype_iter_right_empty_unmatch
    (d : List SpecTec.deftype) (a : SpecTec.valtype)
    (as : List SpecTec.valtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0»
          d (a :: as) []⟩)
      start .unmatch start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_resulttype:case_1:iter:0_clauses»
        d (a :: as) []) ())
    start .unmatch start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_resulttype:case_1:iter:0:clause:0»
        d (a :: as) []) start .unmatch start
    exact SpecTecExecution.Eval.unmatch
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
          d (a :: as) []) start .unmatch start
      exact SpecTecExecution.Eval.unmatch
    · exact SpecTecExecution.firstSuccess_nil () start

end properties.wasm_module_not_ok.Rejection
