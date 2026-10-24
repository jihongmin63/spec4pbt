import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchResulttypeValidation

theorem match_iter_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.«Match_resulttype:rule:iter:0»
        c [] []⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Match_resulttype:rule:iter:0_clauses» c [] []) ())
    n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_success
  exact SpecTecExecution.Eval.pure ()

theorem match_iter_cons_success_iff
    (c : SpecTec.context) (t₁ t₂ : SpecTec.valtype)
    (rest₁ rest₂ : List SpecTec.valtype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.«Match_resulttype:rule:iter:0»
        c (t₁ :: rest₁) (t₂ :: rest₂)⟩)
      n (.success (.of ())) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_valtype» c.TYPES t₁ t₂⟩)
        n (.success (.of true)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Match_resulttype:rule:iter:0»
            c rest₁ rest₂⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Match_resulttype:rule:iter:0:clause:0»
            c (t₁ :: rest₁) (t₂ :: rest₂))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«Match_resulttype:rule:iter:0:clause:1»
              c (t₁ :: rest₁) (t₂ :: rest₂)] ()))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.unmatch) n (.success (.of ())) finalSupply at hfirst
        cases hfirst
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Match_resulttype:rule:iter:0:clause:1»
              c (t₁ :: rest₁) (t₂ :: rest₂))
            (fun _ => .unmatch))
          n (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Match_resulttype:rule:iter:0:clause:1» at hsecond
          cases hsecond with
          | bind_success hmatch htail =>
            rename_i middle b
            cases htail with
            | bind_success hguard htail =>
              cases hguard with
              | guard_true htrue =>
                cases htrue
                cases htail with
                | bind_success hrest hpure =>
                  cases hpure with
                  | pure => exact ⟨middle, hmatch, hrest⟩
        | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨middle, hmatch, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Match_resulttype:rule:iter:0_clauses»
          c (t₁ :: rest₁) (t₂ :: rest₂)) ())
      n (.success (.of ())) finalSupply
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Match_resulttype:rule:iter:0:clause:0»
          c (t₁ :: rest₁) (t₂ :: rest₂)) n .unmatch n
      exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Match_resulttype:rule:iter:0:clause:1»
          c (t₁ :: rest₁) (t₂ :: rest₂))
        n (.success (.of ())) finalSupply
      unfold SpecTec.«Match_resulttype:rule:iter:0:clause:1»
      apply SpecTecExecution.Eval.bind_success hmatch
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success hrest
        exact SpecTecExecution.Eval.pure ()

theorem match_resulttype_success_iff
    (c : SpecTec.context)
    (ts₁ ts₂ : List SpecTec.valtype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Match_resulttype c ts₁ ts₂⟩)
      n (.success (.of ())) finalSupply ↔
    ts₂.length = ts₁.length ∧
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Match_resulttype:rule:iter:0»
          c ts₁ ts₂⟩)
      n (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Match_resulttype:clause:0» c ts₁ ts₂)
          (fun _ => .unmatch))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«Match_resulttype:clause:0» at hclause
        cases hclause with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true hlength =>
            cases htail with
            | bind_success hiter hpure =>
              cases hpure with
              | pure => exact ⟨hlength, hiter⟩
      | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨hlength, hiter⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Match_resulttype_clauses c ts₁ ts₂) ())
      n (.success (.of ())) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Match_resulttype:clause:0» c ts₁ ts₂)
      n (.success (.of ())) finalSupply
    unfold SpecTec.«Match_resulttype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hlength
    · apply SpecTecExecution.Eval.bind_success hiter
      exact SpecTecExecution.Eval.pure ()

theorem match_resulttype_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Match_resulttype c [] []⟩)
      n (.success (.of ())) n :=
  (match_resulttype_success_iff c [] [] n n).2
    ⟨rfl, match_iter_nil_total c n⟩

end properties.wasm_module_ok.MatchResulttypeValidation
