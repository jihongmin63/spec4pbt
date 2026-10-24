import properties.wasm_module_not_ok.MatchReftypeTrace

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_valtype_ref_true_iff
    (d : List SpecTec.deftype) (rt₁ rt₂ : SpecTec.reftype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» d
        (.RefT rt₁) (.RefT rt₂)⟩)
      start (.success (.of true)) finalSupply ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_reftype» d rt₁ rt₂⟩)
      start (.success (.of true)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$match_valtype_clauses» d (.RefT rt₁) (.RefT rt₂)) ())
        start (.success (.of true)) finalSupply at hbody
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«$match_valtype:clause:0» d (.RefT rt₁) (.RefT rt₂))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_valtype:clause:1» d (.RefT rt₁) (.RefT rt₂),
             fun _ => SpecTec.«$match_valtype:clause:2» d (.RefT rt₁) (.RefT rt₂),
             fun _ => SpecTec.«$match_valtype:clause:3» d (.RefT rt₁) (.RefT rt₂),
             fun _ => SpecTec.«$match_valtype:clause:4» d (.RefT rt₁) (.RefT rt₂)] ()))
        start (.success (.of true)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_valtype:clause:0» at hfirst
          cases hfirst with
          | bind_success hg _ =>
              cases hg with
              | guard_true hbad => cases hbad
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«$match_valtype:clause:1» d (.RefT rt₁) (.RefT rt₂))
              (fun _ => SpecTecExecution.firstSuccess
                [fun _ => SpecTec.«$match_valtype:clause:2» d (.RefT rt₁) (.RefT rt₂),
                 fun _ => SpecTec.«$match_valtype:clause:3» d (.RefT rt₁) (.RefT rt₂),
                 fun _ => SpecTec.«$match_valtype:clause:4» d (.RefT rt₁) (.RefT rt₂)] ()))
            start (.success (.of true)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
              unfold SpecTec.«$match_valtype:clause:1» at hsecond
              cases hsecond with
              | bind_success hg _ =>
                  cases hg with
                  | guard_true hbad => cases hbad
          | orElse_unmatch _ htail2 =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (.orElse (SpecTec.«$match_valtype:clause:2» d (.RefT rt₁) (.RefT rt₂))
                  (fun _ => SpecTecExecution.firstSuccess
                    [fun _ => SpecTec.«$match_valtype:clause:3» d (.RefT rt₁) (.RefT rt₂),
                     fun _ => SpecTec.«$match_valtype:clause:4» d (.RefT rt₁) (.RefT rt₂)] ()))
                start (.success (.of true)) finalSupply at htail2
              cases htail2 with
              | orElse_success hthird =>
                  unfold SpecTec.«$match_valtype:clause:2» at hthird
                  cases hthird with
                  | bind_success hg1 hrest =>
                      cases hg1 with
                      | guard_true _ =>
                          cases hrest with
                          | bind_success hg2 hrest =>
                              cases hg2 with
                              | guard_true _ =>
                                  cases hrest with
                                  | bind_success hchild hpure =>
                                      cases hpure with
                                      | pure => exact hchild
              | orElse_unmatch _ htail3 =>
                  change SpecTecExecution.Eval SpecTec.specTecProgram
                    (.orElse (SpecTec.«$match_valtype:clause:3» d (.RefT rt₁) (.RefT rt₂))
                      (fun _ => SpecTecExecution.firstSuccess
                        [fun _ => SpecTec.«$match_valtype:clause:4»
                          d (.RefT rt₁) (.RefT rt₂)] ()))
                    start (.success (.of true)) finalSupply at htail3
                  cases htail3 with
                  | orElse_success hfourth =>
                      unfold SpecTec.«$match_valtype:clause:3» at hfourth
                      cases hfourth with
                      | bind_success hg _ =>
                          cases hg with
                          | guard_true hbad => cases hbad
                  | orElse_unmatch _ htail4 =>
                      change SpecTecExecution.Eval SpecTec.specTecProgram
                        (.orElse (SpecTec.«$match_valtype:clause:4»
                          d (.RefT rt₁) (.RefT rt₂)) (fun _ => .unmatch))
                        start (.success (.of true)) finalSupply at htail4
                      cases htail4 with
                      | orElse_success hlast =>
                          change SpecTecExecution.Eval SpecTec.specTecProgram
                            (.pure false) start (.success (.of true)) finalSupply
                            at hlast
                          cases hlast
                      | orElse_unmatch _ hnil => cases hnil
  · intro hchild
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_valtype_clauses» d (.RefT rt₁) (.RefT rt₂)) ())
      start (.success (.of true)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_valtype:clause:0» d (.RefT rt₁) (.RefT rt₂))
        start .unmatch start
      unfold SpecTec.«$match_valtype:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:valtype:NumT»])
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_valtype:clause:1» d (.RefT rt₁) (.RefT rt₂))
          start .unmatch start
        unfold SpecTec.«$match_valtype:clause:1»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:VecT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_valtype:clause:2» d (.RefT rt₁) (.RefT rt₂))
          start (.success (.of true)) finalSupply
        unfold SpecTec.«$match_valtype:clause:2»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:valtype:RefT»])
        · apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true
              (by simp [SpecTec.«exec:match:valtype:RefT»])
          · apply SpecTecExecution.Eval.bind_success hchild
            exact SpecTecExecution.Eval.pure true

end properties.wasm_module_not_ok.Rejection
