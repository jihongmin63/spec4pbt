import properties.wasm_module_not_ok.MatchArraytypeTrace

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_strtype_func_true_iff
    (d : List SpecTec.deftype) (f₁ f₂ : SpecTec.functype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d
        (.DefFuncT f₁) (.DefFuncT f₂)⟩)
      start (.success (.of true)) finalSupply ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_functype» d f₁ f₂⟩)
      start (.success (.of true)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_strtype:clause:0» d
            (.DefFuncT f₁) (.DefFuncT f₂))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_strtype:clause:1» d
              (.DefFuncT f₁) (.DefFuncT f₂),
             fun _ => SpecTec.«$match_strtype:clause:2» d
              (.DefFuncT f₁) (.DefFuncT f₂),
             fun _ => SpecTec.«$match_strtype:clause:3» d
              (.DefFuncT f₁) (.DefFuncT f₂)] ()))
        start (.success (.of true)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_strtype:clause:0» at hfirst
          cases hfirst with
          | bind_success hg _ =>
              cases hg with
              | guard_true hbad => cases hbad
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«$match_strtype:clause:1» d
                (.DefFuncT f₁) (.DefFuncT f₂))
              (fun _ => SpecTecExecution.firstSuccess
                [fun _ => SpecTec.«$match_strtype:clause:2» d
                  (.DefFuncT f₁) (.DefFuncT f₂),
                 fun _ => SpecTec.«$match_strtype:clause:3» d
                  (.DefFuncT f₁) (.DefFuncT f₂)] ()))
            start (.success (.of true)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
              unfold SpecTec.«$match_strtype:clause:1» at hsecond
              cases hsecond with
              | bind_success hg _ =>
                  cases hg with
                  | guard_true hbad => cases hbad
          | orElse_unmatch _ htail2 =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (.orElse
                  (SpecTec.«$match_strtype:clause:2» d
                    (.DefFuncT f₁) (.DefFuncT f₂))
                  (fun _ => SpecTecExecution.firstSuccess
                    [fun _ => SpecTec.«$match_strtype:clause:3» d
                      (.DefFuncT f₁) (.DefFuncT f₂)] ()))
                start (.success (.of true)) finalSupply at htail2
              cases htail2 with
              | orElse_success hthird =>
                  unfold SpecTec.«$match_strtype:clause:2» at hthird
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
                    (.orElse
                      (SpecTec.«$match_strtype:clause:3» d
                        (.DefFuncT f₁) (.DefFuncT f₂)) (fun _ => .unmatch))
                    start (.success (.of true)) finalSupply at htail3
                  cases htail3 with
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
        (SpecTec.«$match_strtype_clauses» d
          (.DefFuncT f₁) (.DefFuncT f₂)) ())
      start (.success (.of true)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:0» d
          (.DefFuncT f₁) (.DefFuncT f₂)) start .unmatch start
      unfold SpecTec.«$match_strtype:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:strtype:DefStructT»])
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:1» d
            (.DefFuncT f₁) (.DefFuncT f₂)) start .unmatch start
        unfold SpecTec.«$match_strtype:clause:1»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_strtype:clause:2» d
            (.DefFuncT f₁) (.DefFuncT f₂))
          start (.success (.of true)) finalSupply
        unfold SpecTec.«$match_strtype:clause:2»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
        · apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true
              (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
          · apply SpecTecExecution.Eval.bind_success hchild
            exact SpecTecExecution.Eval.pure true

theorem match_strtype_array_true_iff
    (d : List SpecTec.deftype) (a₁ a₂ : SpecTec.arraytype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d
        (.DefArrayT a₁) (.DefArrayT a₂)⟩)
      start (.success (.of true)) finalSupply ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_arraytype» d a₁ a₂⟩)
      start (.success (.of true)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_strtype:clause:0» d
            (.DefArrayT a₁) (.DefArrayT a₂))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_strtype:clause:1» d
              (.DefArrayT a₁) (.DefArrayT a₂),
             fun _ => SpecTec.«$match_strtype:clause:2» d
              (.DefArrayT a₁) (.DefArrayT a₂),
             fun _ => SpecTec.«$match_strtype:clause:3» d
              (.DefArrayT a₁) (.DefArrayT a₂)] ()))
        start (.success (.of true)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_strtype:clause:0» at hfirst
          cases hfirst with
          | bind_success hg _ =>
              cases hg with
              | guard_true hbad => cases hbad
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«$match_strtype:clause:1» d
                (.DefArrayT a₁) (.DefArrayT a₂))
              (fun _ => SpecTecExecution.firstSuccess
                [fun _ => SpecTec.«$match_strtype:clause:2» d
                  (.DefArrayT a₁) (.DefArrayT a₂),
                 fun _ => SpecTec.«$match_strtype:clause:3» d
                  (.DefArrayT a₁) (.DefArrayT a₂)] ()))
            start (.success (.of true)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
              unfold SpecTec.«$match_strtype:clause:1» at hsecond
              cases hsecond with
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
          | orElse_unmatch _ htail2 =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (.orElse
                  (SpecTec.«$match_strtype:clause:2» d
                    (.DefArrayT a₁) (.DefArrayT a₂))
                  (fun _ => SpecTecExecution.firstSuccess
                    [fun _ => SpecTec.«$match_strtype:clause:3» d
                      (.DefArrayT a₁) (.DefArrayT a₂)] ()))
                start (.success (.of true)) finalSupply at htail2
              cases htail2 with
              | orElse_success hthird =>
                  unfold SpecTec.«$match_strtype:clause:2» at hthird
                  cases hthird with
                  | bind_success hg _ =>
                      cases hg with
                      | guard_true hbad => cases hbad
              | orElse_unmatch _ htail3 =>
                  change SpecTecExecution.Eval SpecTec.specTecProgram
                    (.orElse
                      (SpecTec.«$match_strtype:clause:3» d
                        (.DefArrayT a₁) (.DefArrayT a₂)) (fun _ => .unmatch))
                    start (.success (.of true)) finalSupply at htail3
                  cases htail3 with
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
        (SpecTec.«$match_strtype_clauses» d
          (.DefArrayT a₁) (.DefArrayT a₂)) ())
      start (.success (.of true)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:0» d
          (.DefArrayT a₁) (.DefArrayT a₂)) start .unmatch start
      unfold SpecTec.«$match_strtype:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:strtype:DefStructT»])
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:1» d
          (.DefArrayT a₁) (.DefArrayT a₂))
        start (.success (.of true)) finalSupply
      unfold SpecTec.«$match_strtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
        · apply SpecTecExecution.Eval.bind_success hchild
          exact SpecTecExecution.Eval.pure true

theorem match_strtype_struct_true_iff
    (d : List SpecTec.deftype) (s₁ s₂ : SpecTec.structtype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» d
        (.DefStructT s₁) (.DefStructT s₂)⟩)
      start (.success (.of true)) finalSupply ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_structtype» d s₁ s₂⟩)
      start (.success (.of true)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_strtype:clause:0» d
            (.DefStructT s₁) (.DefStructT s₂))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_strtype:clause:1» d
              (.DefStructT s₁) (.DefStructT s₂),
             fun _ => SpecTec.«$match_strtype:clause:2» d
              (.DefStructT s₁) (.DefStructT s₂),
             fun _ => SpecTec.«$match_strtype:clause:3» d
              (.DefStructT s₁) (.DefStructT s₂)] ()))
        start (.success (.of true)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_strtype:clause:0» at hfirst
          cases hfirst with
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
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«$match_strtype:clause:1» d
                (.DefStructT s₁) (.DefStructT s₂))
              (fun _ => SpecTecExecution.firstSuccess
                [fun _ => SpecTec.«$match_strtype:clause:2» d
                  (.DefStructT s₁) (.DefStructT s₂),
                 fun _ => SpecTec.«$match_strtype:clause:3» d
                  (.DefStructT s₁) (.DefStructT s₂)] ()))
            start (.success (.of true)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
              unfold SpecTec.«$match_strtype:clause:1» at hsecond
              cases hsecond with
              | bind_success hg _ =>
                  cases hg with
                  | guard_true hbad => cases hbad
          | orElse_unmatch _ htail2 =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (.orElse
                  (SpecTec.«$match_strtype:clause:2» d
                    (.DefStructT s₁) (.DefStructT s₂))
                  (fun _ => SpecTecExecution.firstSuccess
                    [fun _ => SpecTec.«$match_strtype:clause:3» d
                      (.DefStructT s₁) (.DefStructT s₂)] ()))
                start (.success (.of true)) finalSupply at htail2
              cases htail2 with
              | orElse_success hthird =>
                  unfold SpecTec.«$match_strtype:clause:2» at hthird
                  cases hthird with
                  | bind_success hg _ =>
                      cases hg with
                      | guard_true hbad => cases hbad
              | orElse_unmatch _ htail3 =>
                  change SpecTecExecution.Eval SpecTec.specTecProgram
                    (.orElse
                      (SpecTec.«$match_strtype:clause:3» d
                        (.DefStructT s₁) (.DefStructT s₂)) (fun _ => .unmatch))
                    start (.success (.of true)) finalSupply at htail3
                  cases htail3 with
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
        (SpecTec.«$match_strtype_clauses» d
          (.DefStructT s₁) (.DefStructT s₂)) ())
      start (.success (.of true)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:0» d
        (.DefStructT s₁) (.DefStructT s₂))
      start (.success (.of true)) finalSupply
    unfold SpecTec.«$match_strtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:strtype:DefStructT»])
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:strtype:DefStructT»])
      · apply SpecTecExecution.Eval.bind_success hchild
        exact SpecTecExecution.Eval.pure true

end properties.wasm_module_not_ok.Rejection
