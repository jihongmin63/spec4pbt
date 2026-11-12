import properties.wasm_module_not_ok.MatchNullValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_reftype_true_iff (d : List SpecTec.deftype)
    (n₁ n₂ : SpecTec.null) (ht₁ ht₂ : SpecTec.heaptype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_reftype» d
          (.«% %» n₁ ht₁) (.«% %» n₂ ht₂)⟩)
      start (.success (.of true)) finalSupply ↔
    matchNull n₁ n₂ = true ∧
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_heaptype» d ht₁ ht₂⟩)
      start (.success (.of true)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_reftype:clause:0» d
            (.«% %» n₁ ht₁) (.«% %» n₂ ht₂))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_reftype:clause:1» d
              (.«% %» n₁ ht₁) (.«% %» n₂ ht₂)] ()))
        start (.success (.of true)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_reftype:clause:0» at hfirst
          cases hfirst with
          | bind_success hnull hrest =>
              obtain ⟨hnullvalue, hmiddle⟩ :=
                match_null_deterministic n₁ n₂ start _ _ hnull
              cases hnullvalue
              subst hmiddle
              cases hrest with
              | bind_success hheap hrest =>
                  cases hrest with
                  | bind_success hguard hpure =>
                      cases hpure with
                      | pure =>
                          cases hguard with
                          | guard_true hboth =>
                              obtain ⟨hn, hh⟩ := hboth
                              cases hh
                              exact ⟨hn, hheap⟩
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«$match_reftype:clause:1» d
                (.«% %» n₁ ht₁) (.«% %» n₂ ht₂))
              (fun _ => .unmatch))
            start (.success (.of true)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (.pure false) start (.success (.of true)) finalSupply
                at hsecond
              cases hsecond
          | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨hnullvalue, hheap⟩
    have hnull : SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_null» n₁ n₂⟩)
        start (.success (.of true)) start := by
      simpa [hnullvalue] using match_null_total n₁ n₂ start
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_reftype_clauses» d
          (.«% %» n₁ ht₁) (.«% %» n₂ ht₂)) ())
      start (.success (.of true)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_reftype:clause:0» d
        (.«% %» n₁ ht₁) (.«% %» n₂ ht₂))
      start (.success (.of true)) finalSupply
    unfold SpecTec.«$match_reftype:clause:0»
    apply SpecTecExecution.Eval.bind_success hnull
    apply SpecTecExecution.Eval.bind_success hheap
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true ⟨rfl, rfl⟩
    · exact SpecTecExecution.Eval.pure true

end properties.wasm_module_not_ok.Rejection
