import properties.wasm_module_not_ok.MatchValtypeBase

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_arraytype_success_iff (d : List SpecTec.deftype)
    (f₁ f₂ : SpecTec.fieldtype) (start finalSupply : Nat) (r : Bool) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_arraytype» d
        (.ArrayT f₁) (.ArrayT f₂)⟩)
      start (.success (.of r)) finalSupply ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» d f₁ f₂⟩)
      start (.success (.of r)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«$match_arraytype:clause:0» d (.ArrayT f₁) (.ArrayT f₂))
          (fun _ => .unmatch))
        start (.success (.of r)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
          unfold SpecTec.«$match_arraytype:clause:0» at hfirst
          cases hfirst with
          | bind_success hfield hpure =>
              cases hpure with
              | pure => exact hfield
      | orElse_unmatch _ htail => cases htail
  · intro hfield
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_arraytype_clauses» d (.ArrayT f₁) (.ArrayT f₂)) ())
      start (.success (.of r)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_arraytype:clause:0» d (.ArrayT f₁) (.ArrayT f₂))
      start (.success (.of r)) finalSupply
    unfold SpecTec.«$match_arraytype:clause:0»
    apply SpecTecExecution.Eval.bind_success hfield
    exact SpecTecExecution.Eval.pure r

end properties.wasm_module_not_ok.Rejection
