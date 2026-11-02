import properties.wasm_module_ok.CandidateValMatch
import properties.wasm_module_ok.MatchResulttypeValidation
import Mathlib.Data.List.Forall2

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstConstructiveMatchList

/-- Pointwise executable matches construct the translated ordered list call. -/
theorem match_iter_of_pairs (c : SpecTec.context)
    (hready : CandidateTypeReady.Ready c) :
    ∀ {actual required : List SpecTec.valtype},
      List.Forall₂
        (fun a r => CandidateValMatch.candidateValMatch c a r = true)
        actual required →
      (∀ a ∈ actual, CandidateValMatch.InTableVal c a) →
      (∀ r ∈ required, CandidateValMatch.InTableVal c r) →
      ∀ n : Nat,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Unit, SpecTec.Call.«Match_resulttype:rule:iter:0»
            c actual required⟩)
          n (.success (.of ())) n := by
  intro actual required hpairs
  induction hpairs with
  | nil =>
    intro _ _ n
    exact MatchResulttypeValidation.match_iter_nil_total c n
  | @cons a r as rs hpair htail ih =>
    intro hactual hrequired n
    apply (MatchResulttypeValidation.match_iter_cons_success_iff
      c a r as rs n n).2
    refine ⟨n, ?_, ?_⟩
    · simpa [hpair] using
        (CandidateValMatch.candidate_val_match_total c a r n
          hready (hactual a (by simp))
          (hrequired r (by simp)))
    · apply ih
      · intro v hv
        exact hactual v (by simp [hv])
      · intro v hv
        exact hrequired v (by simp [hv])

theorem match_resulttype_of_pairs (c : SpecTec.context)
    (actual required : List SpecTec.valtype) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hpairs : List.Forall₂
      (fun a r => CandidateValMatch.candidateValMatch c a r = true)
      actual required)
    (hactual : ∀ a ∈ actual, CandidateValMatch.InTableVal c a)
    (hrequired : ∀ r ∈ required, CandidateValMatch.InTableVal c r) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Match_resulttype c
        actual required⟩)
      n (.success (.of ())) n := by
  apply (MatchResulttypeValidation.match_resulttype_success_iff
    c actual required n n).2
  exact ⟨hpairs.length_eq.symm,
    match_iter_of_pairs c hready hpairs hactual hrequired n⟩

end properties.wasm_module_ok.ConstConstructiveMatchList
