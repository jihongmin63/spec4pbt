import properties.wasm_module_ok.ConstConstructiveMatchList
import properties.wasm_module_ok.ConstStaticAgreement

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstConstructiveMatchStatic

/-- Ordered operand matching remains valid after local initialization changes
the context but preserves its type table. -/
theorem match_resulttype_at_static_context
    (origin current : SpecTec.context)
    (actual required : List SpecTec.valtype) (n : Nat)
    (hstatic : ConstStaticAgreement.StaticAgreement origin current)
    (hready : CandidateTypeReady.Ready origin)
    (hpairs : List.Forall₂
      (fun a r => CandidateValMatch.candidateValMatch origin a r = true)
      actual required)
    (hactual : ∀ a ∈ actual, CandidateValMatch.InTableVal origin a)
    (hrequired : ∀ r ∈ required,
      CandidateValMatch.InTableVal origin r) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype current
        actual required⟩)
      n (.success (.of ())) n := by
  have hpairsCurrent : List.Forall₂
      (fun a r => CandidateValMatch.candidateValMatch current a r = true)
      actual required := by
    induction hpairs with
    | nil => exact List.Forall₂.nil
    | @cons a r as rs hpair htail ih =>
      apply List.Forall₂.cons
      · rw [ConstClosureStatic.candidate_val_match_of_types_eq
          current origin hstatic.types]
        exact hpair
      · exact ih
          (by
            intro v hv
            exact hactual v (by simp [hv]))
          (by
            intro v hv
            exact hrequired v (by simp [hv]))
  exact ConstConstructiveMatchList.match_resulttype_of_pairs
    current actual required n
    (ConstStaticAgreement.ready origin current hstatic hready)
    hpairsCurrent
    (by
      intro a ha
      exact ConstStaticAgreement.in_table_val origin current
        hstatic a (hactual a ha))
    (by
      intro r hr
      exact ConstStaticAgreement.in_table_val origin current
        hstatic r (hrequired r hr))

end properties.wasm_module_ok.ConstConstructiveMatchStatic
