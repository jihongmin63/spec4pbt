import properties.wasm_module_ok.ConstructiveBodyEnvironment
import properties.wasm_module_ok.MatchResulttypeLocal
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMatchers
open SpecTec properties.wasm_module_ok

theorem all_matched (c : context) (xs ys : List valtype) :
    MatchResulttypeConditional.allMatched (CandidateValMatch.candidateValMatch c) xs ys=
      MatchResulttypeDecision.matchPairs c xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih => cases ys <;> simp [MatchResulttypeConditional.allMatched,MatchResulttypeDecision.matchPairs,ih]

theorem pairs_length (c : context) (xs ys : List valtype)
    (h : MatchResulttypeDecision.matchPairs c xs ys=true) : ys.length=xs.length := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [MatchResulttypeDecision.matchPairs]
  | cons x xs ih =>
    cases ys with
    | nil => simp [MatchResulttypeDecision.matchPairs] at h
    | cons y ys =>
      have hh : CandidateValMatch.candidateValMatch c x y=true ∧ MatchResulttypeDecision.matchPairs c xs ys=true := by simpa [MatchResulttypeDecision.matchPairs] using h
      simpa using congrArg Nat.succ (ih ys hh.2)

theorem result_matches (c : context) (xs ys : List valtype) :
    MatchResulttypeConditional.matchResulttypeResult (CandidateValMatch.candidateValMatch c) xs ys=
      MatchResulttypeDecision.matchPairs c xs ys := by
  rw [MatchResulttypeConditional.matchResulttypeResult,all_matched]
  cases h : MatchResulttypeDecision.matchPairs c xs ys with
  | false => simp
  | true => simp [pairs_length c xs ys h]

theorem result_total (c : context) (xs ys : List valtype) (n : Nat)
    (hr : CandidateTypeReady.Ready c)
    (hx : ∀t∈xs,CandidateValMatch.InTableVal c t)
    (hy : ∀t∈ys,CandidateValMatch.InTableVal c t) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,Call.«$match_resulttype» c.TYPES xs ys⟩)
      n (.success (.of (MatchResulttypeDecision.matchPairs c xs ys))) n := by
  rw [←result_matches]
  exact MatchResulttypeLocal.match_resulttype_total_of_local_valtype_at c.TYPES
    (CandidateValMatch.candidateValMatch c) xs ys n (fun x hxm y hym =>
      CandidateValMatch.candidate_val_match_total c x y n hr (hx x hxm) (hy y hym))

theorem result_exact (c : context) (xs ys : List valtype) (value : Bool) (start finish : Nat)
    (hr : CandidateTypeReady.Ready c)
    (hx : ∀t∈xs,CandidateValMatch.InTableVal c t)
    (hy : ∀t∈ys,CandidateValMatch.InTableVal c t) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,Call.«$match_resulttype» c.TYPES xs ys⟩)
      start (.success (.of value)) finish ↔
    value=MatchResulttypeDecision.matchPairs c xs ys ∧ finish=start := by
  constructor
  · intro h
    obtain ⟨he,hf⟩ := properties.wasm_module_ok.Execution.eval_deterministic h (result_total c xs ys start hr hx hy)
    cases he
    exact ⟨rfl,hf⟩
  · rintro ⟨rfl,rfl⟩
    exact result_total c xs ys finish hr hx hy

#print axioms result_exact
end properties.wasm_module_ok.ConstructiveBodyMatchers
