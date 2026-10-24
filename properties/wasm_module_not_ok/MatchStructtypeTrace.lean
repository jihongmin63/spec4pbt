import properties.wasm_module_not_ok.MatchStructtypeIterTrace

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_structtype_true_of_iter (d : List SpecTec.deftype)
    (fs₁ fs₂ : List SpecTec.fieldtype)
    (start finalSupply : Nat)
    (hlen : fs₂.length ≤ fs₁.length)
    (hiter : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_structtype:case_1:iter:0»
          d (fs₁.take fs₂.length) fs₂⟩)
      start (.success (.of ())) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_structtype» d
        (.StructT fs₁) (.StructT fs₂)⟩)
      start (.success (.of true)) finalSupply := by
  have hslice : fs₂.length =
      (fs₁.take fs₂.length).length := by
    simp [List.length_take, Nat.min_eq_left hlen]
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_structtype_clauses» d
        (.StructT fs₁) (.StructT fs₂)) ())
    start (.success (.of true)) finalSupply
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_structtype:clause:0» d
      (.StructT fs₁) (.StructT fs₂))
    start (.success (.of true)) finalSupply
  unfold SpecTec.«$match_structtype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true hlen
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.orElse_success
        (SpecTecExecution.Eval.guard_true (by simpa using hlen))
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simpa using hslice)
      · apply SpecTecExecution.Eval.bind_success
          (by simpa using hiter)
        exact SpecTecExecution.Eval.pure true

theorem match_structtype_true_iff (d : List SpecTec.deftype)
    (fs₁ fs₂ : List SpecTec.fieldtype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_structtype» d
        (.StructT fs₁) (.StructT fs₂)⟩)
      start (.success (.of true)) finalSupply ↔
    fs₂.length ≤ fs₁.length ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«$match_structtype:case_1:iter:0»
            d (fs₁.take fs₂.length) fs₂⟩)
        start (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_structtype:clause:0» d
            (.StructT fs₁) (.StructT fs₂))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$match_structtype:clause:1» d
              (.StructT fs₁) (.StructT fs₂)] ()))
        start (.success (.of true)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_structtype:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard hrest =>
              cases hguard with
              | guard_true hlen =>
                  cases hrest with
                  | bind_success hrequire hrest =>
                      cases hrequire with
                      | orElse_success hreqguard =>
                          cases hreqguard with
                          | guard_true _ =>
                              cases hrest with
                              | bind_success hslice hrest =>
                                  cases hslice with
                                  | guard_true _ =>
                                      cases hrest with
                                      | bind_success hiter hpure =>
                                          cases hpure with
                                          | pure =>
                                              exact ⟨hlen, by simpa using hiter⟩
                      | orElse_unmatch _ habort => cases habort
      | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse
              (SpecTec.«$match_structtype:clause:1» d
                (.StructT fs₁) (.StructT fs₂)) (fun _ => .unmatch))
            start (.success (.of true)) finalSupply at htail
          cases htail with
          | orElse_success hfalse =>
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (.pure false) start (.success (.of true)) finalSupply
                at hfalse
              cases hfalse
          | orElse_unmatch _ hnil => cases hnil
  · rintro ⟨hlen, hiter⟩
    exact match_structtype_true_of_iter d fs₁ fs₂
      start finalSupply hlen hiter

end properties.wasm_module_not_ok.Rejection
