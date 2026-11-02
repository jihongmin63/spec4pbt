import properties.wasm_module_ok.MatchResulttypeDecision
import properties.wasm_module_ok.PopGeneralValidation
import properties.wasm_module_ok.PopResult
import properties.wasm_module_ok.PopMatchExtraction
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.PopNoEllipsesDecision

def popResult (c : SpecTec.context)
    (need available : List SpecTec.valtype) :
    Option SpecTec.inferresulttype :=
  if need.length ≤ available.length then
    if MatchResulttypeDecision.matchPairs c
        (available.drop (available.length - need.length)) need then
      some (.NoEllipses,
        available.take (available.length - need.length))
    else none
  else none

theorem pop_result_sound
    (c : SpecTec.context)
    (need available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hneed : ∀ t ∈ need, CandidateValMatch.InTableVal c t)
    (havailable : ∀ t ∈ available,
      CandidateValMatch.InTableVal c t)
    (hresult : popResult c need available = some result) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, need) (.NoEllipses, available)⟩)
      n (.success (.of result)) n := by
  by_cases hlength : need.length ≤ available.length
  · simp only [popResult, if_pos hlength] at hresult
    cases hmatch : MatchResulttypeDecision.matchPairs c
        (available.drop (available.length - need.length)) need with
    | false => simp [hmatch] at hresult
    | true =>
      simp only [hmatch, ite_true, Option.some.injEq] at hresult
      subst result
      have hdrop : ∀ t ∈ available.drop
          (available.length - need.length),
          CandidateValMatch.InTableVal c t := by
        intro t ht
        exact havailable t (List.mem_of_mem_drop ht)
      have hmatching :=
        (MatchResulttypeDecision.match_pairs_iff_resulttype
          c (available.drop (available.length - need.length)) need n
          hready hdrop hneed).1 hmatch
      exact PopGeneralValidation.pop_noellipses_of_match
        c need available n n hlength hmatching
  · simp [popResult, hlength] at hresult

theorem pop_result_complete
    (c : SpecTec.context)
    (need available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hneed : ∀ t ∈ need, CandidateValMatch.InTableVal c t)
    (havailable : ∀ t ∈ available,
      CandidateValMatch.InTableVal c t)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of result)) finish) :
    popResult c need available = some result := by
  obtain ⟨hlength, middle, hmatch⟩ :=
    PopMatchExtraction.pop_noellipses_success_has_match
      c need available result start finish hcall
  have hdrop : ∀ t ∈ available.drop
      (available.length - need.length),
      CandidateValMatch.InTableVal c t := by
    intro t ht
    exact havailable t (List.mem_of_mem_drop ht)
  have hbool :=
    MatchResulttypeDecision.match_pairs_of_resulttype_success
      c (available.drop (available.length - need.length)) need
      middle finish hready hdrop hneed hmatch
  have hr := PopResult.pop_noellipses_success_result
    c need available result start finish hcall
  rw [hr]
  simp [popResult, hlength, hbool]

theorem pop_success_counter
    (c : SpecTec.context)
    (need available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hneed : ∀ t ∈ need, CandidateValMatch.InTableVal c t)
    (havailable : ∀ t ∈ available,
      CandidateValMatch.InTableVal c t)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of result)) finish) :
    finish = start := by
  have hresult := pop_result_complete c need available result
    start finish hready hneed havailable hcall
  have hsame := pop_result_sound c need available result
    start hready hneed havailable hresult
  exact (properties.wasm_module_ok.Execution.eval_deterministic hcall hsame).2

theorem pop_result_iff
    (c : SpecTec.context)
    (need available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hneed : ∀ t ∈ need, CandidateValMatch.InTableVal c t)
    (havailable : ∀ t ∈ available,
      CandidateValMatch.InTableVal c t) :
    popResult c need available = some result ↔
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.Call.«$pop» c
            (.NoEllipses, need) (.NoEllipses, available)⟩)
        n (.success (.of result)) n := by
  exact ⟨pop_result_sound c need available result n
      hready hneed havailable,
    pop_result_complete c need available result n n
      hready hneed havailable⟩

theorem pop_result_iff_any_counters
    (c : SpecTec.context)
    (need available : List SpecTec.valtype)
    (result : SpecTec.inferresulttype)
    (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hneed : ∀ t ∈ need, CandidateValMatch.InTableVal c t)
    (havailable : ∀ t ∈ available,
      CandidateValMatch.InTableVal c t) :
    popResult c need available = some result ∧ finish = start ↔
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.Call.«$pop» c
            (.NoEllipses, need) (.NoEllipses, available)⟩)
        start (.success (.of result)) finish := by
  constructor
  · rintro ⟨hresult, rfl⟩
    exact pop_result_sound c need available result finish
      hready hneed havailable hresult
  · intro hcall
    exact ⟨pop_result_complete c need available result start finish
        hready hneed havailable hcall,
      pop_success_counter c need available result start finish
        hready hneed havailable hcall⟩

end properties.wasm_module_ok.PopNoEllipsesDecision
