import properties.wasm_module_ok.CandidateRectypeStep
import properties.wasm_module_ok.EmptyStageValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateTypesDecision

/-- Check a type list one group at a time, carrying forward only the context
computed from groups that pass their exact closing check. -/
def typesResult (c : SpecTec.context) :
    List SpecTec.type → Option SpecTec.context
  | [] => some c
  | .RecT sts :: ts =>
      if CandidateRectypeDecision.rectypePasses c sts then
        (CandidateRectypeTable.candidateContext c sts).bind
          (fun next => typesResult next ts)
      else none

theorem types_result_of_success
    (c result : SpecTec.context) (ts : List SpecTec.type)
    (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Types_ok c ts⟩)
      start (.success (.of result)) finish) :
    typesResult c ts = some result := by
  induction ts generalizing c result start finish with
  | nil =>
      have heq := ValidatedTypeChain.types_ok_nil_eq
        c result start finish h
      subst result
      rfl
  | cons t ts ih =>
      cases t with
      | RecT sts =>
          obtain ⟨middle, next, hhead, htail⟩ :=
            TypesPrefixValidation.types_ok_cons_trace
              c result (.RecT sts) ts start finish h
          have hrect :=
            TypesPrefixValidation.type_ok_rectype_trace
              c next sts start middle hhead
          obtain ⟨hpass, hcontext⟩ :=
            CandidateRectypeStep.passes_of_success
              c next sts start middle hc hrect
          have hnext : ValidatedTypeChain.ValidatedTypes next :=
            .append c next sts start middle hc hrect
          have hresult := ih next result middle finish hnext htail
          simpa [typesResult, hpass, hcontext] using hresult

theorem types_success_of_result
    (c result : SpecTec.context) (ts : List SpecTec.type)
    (n : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (hresult : typesResult c ts = some result) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Types_ok c ts⟩)
      n (.success (.of result)) n := by
  induction ts generalizing c result n with
  | nil =>
      have heq : c = result := Option.some.inj hresult
      subst result
      exact EmptyStageValidation.types_nil_total c n
  | cons t ts ih =>
      cases t with
      | RecT sts =>
          by_cases hpass : CandidateRectypeDecision.rectypePasses c sts = true
          · cases hcontext : CandidateRectypeTable.candidateContext c sts with
            | none =>
                simp [typesResult, hpass, hcontext] at hresult
            | some next =>
                have htail : typesResult next ts = some result := by
                  simpa [typesResult, hpass, hcontext] using hresult
                have hrect :=
                  CandidateRectypeStep.success_of_passes
                    c next sts n hc hpass hcontext
                have hnext : ValidatedTypeChain.ValidatedTypes next :=
                  .append c next sts n n hc hrect
                exact CandidateTypesTrace.types_ok_cons_of_calls
                  c next result (.RecT sts) ts n n n
                  (CandidateTypesTrace.type_ok_of_rectype
                    c next sts n n hrect)
                  (ih next result n hnext htail)
          · simp [typesResult, hpass] at hresult

theorem types_result_iff_success
    (c result : SpecTec.context) (ts : List SpecTec.type)
    (n : Nat) (hc : ValidatedTypeChain.ValidatedTypes c) :
    typesResult c ts = some result ↔
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context,
          SpecTec.Call.Types_ok c ts⟩)
        n (.success (.of result)) n := by
  exact ⟨types_success_of_result c result ts n hc,
    fun h => types_result_of_success c result ts n n hc h⟩

end properties.wasm_module_ok.CandidateTypesDecision
