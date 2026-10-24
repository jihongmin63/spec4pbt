import properties.wasm_module_not_ok.Rejection

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_functype_success_iff (d : List SpecTec.deftype)
    (as₁ as₂ bs₁ bs₂ : List SpecTec.valtype)
    (start finalSupply : Nat) (r : Bool) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_functype» d
          (.FuncT as₁ as₂) (.FuncT bs₁ bs₂)⟩)
      start (.success (.of r)) finalSupply ↔
    ∃ (middle : Nat) (b₁ b₂ : Bool),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_resulttype» d bs₁ as₁⟩)
        start (.success (.of b₁)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_resulttype» d as₂ bs₂⟩)
        middle (.success (.of b₂)) finalSupply ∧
      r = (b₁ && b₂) := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_functype:clause:0» d
            (.FuncT as₁ as₂) (.FuncT bs₁ bs₂))
          (fun _ => .unmatch))
        start (.success (.of r)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«$match_functype:clause:0» at hfirst
        cases hfirst with
        | bind_success hinput hrest =>
          cases hrest with
          | bind_success houtput hpure =>
            cases hpure with
            | pure => exact ⟨_, _, _, hinput, houtput, rfl⟩
      | orElse_unmatch _ htail => cases htail
  · rintro ⟨middle, b₁, b₂, hinput, houtput, rfl⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_functype_clauses» d
          (.FuncT as₁ as₂) (.FuncT bs₁ bs₂)) ())
      start (.success (.of (b₁ && b₂))) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_functype:clause:0» d
        (.FuncT as₁ as₂) (.FuncT bs₁ bs₂))
      start (.success (.of (b₁ && b₂))) finalSupply
    unfold SpecTec.«$match_functype:clause:0»
    apply SpecTecExecution.Eval.bind_success hinput
    apply SpecTecExecution.Eval.bind_success houtput
    exact SpecTecExecution.Eval.pure (b₁ && b₂)

end properties.wasm_module_not_ok.Rejection
