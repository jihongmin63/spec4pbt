import properties.wasm_module_not_ok.MatchStoragetypeTrace

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_fieldtype_cons_true_iff (d : List SpecTec.deftype)
    (z₁ z₂ : SpecTec.storagetype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» d
        (.FieldT .Cons z₁) (.FieldT .Cons z₂)⟩)
      start (.success (.of true)) finalSupply ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_storagetype» d z₁ z₂⟩)
      start (.success (.of true)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_fieldtype:clause:0» d
            (.FieldT .Cons z₁) (.FieldT .Cons z₂))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_fieldtype:clause:1» d
              (.FieldT .Cons z₁) (.FieldT .Cons z₂),
             fun _ => SpecTec.«$match_fieldtype:clause:2» d
              (.FieldT .Cons z₁) (.FieldT .Cons z₂)] ()))
        start (.success (.of true)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_fieldtype:clause:0» at hfirst
          cases hfirst with
          | bind_success hstor hrest =>
              cases hrest with
              | bind_success hguard hpure =>
                  cases hpure with
                  | pure =>
                      cases hguard with
                      | guard_true hcondition =>
                          cases hcondition.1.2
                          exact hstor
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«$match_fieldtype:clause:1» d
                (.FieldT .Cons z₁) (.FieldT .Cons z₂))
              (fun _ => SpecTecExecution.firstSuccess
                [fun _ => SpecTec.«$match_fieldtype:clause:2» d
                  (.FieldT .Cons z₁) (.FieldT .Cons z₂)] ()))
            start (.success (.of true)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
              unfold SpecTec.«$match_fieldtype:clause:1» at hsecond
              cases hsecond with
              | bind_success _ hrest =>
                  cases hrest with
                  | bind_success _ hrest =>
                      cases hrest with
                      | bind_success hguard _ =>
                          cases hguard with
                          | guard_true hcondition =>
                              cases hcondition.1.2
          | orElse_unmatch _ htail2 =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (.orElse
                  (SpecTec.«$match_fieldtype:clause:2» d
                    (.FieldT .Cons z₁) (.FieldT .Cons z₂))
                  (fun _ => .unmatch))
                start (.success (.of true)) finalSupply at htail2
              cases htail2 with
              | orElse_success hlast =>
                  change SpecTecExecution.Eval SpecTec.specTecProgram
                    (.pure false) start (.success (.of true)) finalSupply
                    at hlast
                  cases hlast
              | orElse_unmatch _ hnil => cases hnil
  · intro hstor
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_fieldtype_clauses» d
          (.FieldT .Cons z₁) (.FieldT .Cons z₂)) ())
      start (.success (.of true)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_fieldtype:clause:0» d
        (.FieldT .Cons z₁) (.FieldT .Cons z₂))
      start (.success (.of true)) finalSupply
    unfold SpecTec.«$match_fieldtype:clause:0»
    apply SpecTecExecution.Eval.bind_success hstor
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true ⟨⟨rfl, rfl⟩, rfl⟩
    · exact SpecTecExecution.Eval.pure true

theorem match_fieldtype_var_true_iff (d : List SpecTec.deftype)
    (z₁ z₂ : SpecTec.storagetype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» d
        (.FieldT .Var z₁) (.FieldT .Var z₂)⟩)
      start (.success (.of true)) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_storagetype» d z₁ z₂⟩)
        start (.success (.of true)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_storagetype» d z₂ z₁⟩)
        middle (.success (.of true)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_fieldtype:clause:0» d
            (.FieldT .Var z₁) (.FieldT .Var z₂))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_fieldtype:clause:1» d
              (.FieldT .Var z₁) (.FieldT .Var z₂),
             fun _ => SpecTec.«$match_fieldtype:clause:2» d
              (.FieldT .Var z₁) (.FieldT .Var z₂)] ()))
        start (.success (.of true)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_fieldtype:clause:0» at hfirst
          cases hfirst with
          | bind_success _ hrest =>
              cases hrest with
              | bind_success hguard _ =>
                  cases hguard with
                  | guard_true hcondition => cases hcondition.2
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«$match_fieldtype:clause:1» d
                (.FieldT .Var z₁) (.FieldT .Var z₂))
              (fun _ => SpecTecExecution.firstSuccess
                [fun _ => SpecTec.«$match_fieldtype:clause:2» d
                  (.FieldT .Var z₁) (.FieldT .Var z₂)] ()))
            start (.success (.of true)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
              unfold SpecTec.«$match_fieldtype:clause:1» at hsecond
              cases hsecond with
              | bind_success hforward hrest =>
                  cases hrest with
                  | bind_success hreverse hrest =>
                      cases hrest with
                      | bind_success hguard hpure =>
                          cases hpure with
                          | pure =>
                              cases hguard with
                              | guard_true hcondition =>
                                  cases hcondition.1.1.2
                                  cases hcondition.2
                                  exact ⟨_, hforward, hreverse⟩
          | orElse_unmatch _ htail2 =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (.orElse
                  (SpecTec.«$match_fieldtype:clause:2» d
                    (.FieldT .Var z₁) (.FieldT .Var z₂))
                  (fun _ => .unmatch))
                start (.success (.of true)) finalSupply at htail2
              cases htail2 with
              | orElse_success hlast =>
                  change SpecTecExecution.Eval SpecTec.specTecProgram
                    (.pure false) start (.success (.of true)) finalSupply
                    at hlast
                  cases hlast
              | orElse_unmatch _ hnil => cases hnil
  · rintro ⟨middle, hforward, hreverse⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_fieldtype_clauses» d
          (.FieldT .Var z₁) (.FieldT .Var z₂)) ())
      start (.success (.of true)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:0» d
          (.FieldT .Var z₁) (.FieldT .Var z₂)) start .unmatch middle
      unfold SpecTec.«$match_fieldtype:clause:0»
      apply SpecTecExecution.Eval.bind_success hforward
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false (by decide)
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:1» d
          (.FieldT .Var z₁) (.FieldT .Var z₂))
        start (.success (.of true)) finalSupply
      unfold SpecTec.«$match_fieldtype:clause:1»
      apply SpecTecExecution.Eval.bind_success hforward
      apply SpecTecExecution.Eval.bind_success hreverse
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
      · exact SpecTecExecution.Eval.pure true

end properties.wasm_module_not_ok.Rejection
