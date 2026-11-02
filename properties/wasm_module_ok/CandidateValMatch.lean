import properties.wasm_module_ok.CandidateHeapMatch
import properties.wasm_module_ok.MatchValtypeLocal
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateValMatch

/-- Only reference values need a heap-table condition. -/
def InTableVal (c : SpecTec.context) (t : SpecTec.valtype) : Prop :=
  ∀ ht, ht ∈ ReadyMatchReachability.sourceValHeaptypes t →
    CandidateHeapMatch.InTable c ht

/-- The pure result of matching two values whose reference heaps are backed
by the ready type table. -/
def candidateValMatch (c : SpecTec.context)
    (u t : SpecTec.valtype) : Bool :=
  MatchValtypeConditional.matchValtypeResult
    (fun h1 h2 =>
      (ReadyHeapMatch.readyHeapMatch c h1 h2).getD false) u t

theorem candidate_val_match_total
    (c : SpecTec.context) (u t : SpecTec.valtype) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hu : InTableVal c u) (ht : InTableVal c t) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_valtype» c.TYPES u t⟩)
      n (.success (.of (candidateValMatch c u t))) n := by
  exact MatchValtypeLocal.match_valtype_total_of_local_heap_at
    c.TYPES (fun h1 h2 =>
      (ReadyHeapMatch.readyHeapMatch c h1 h2).getD false) u t n
    (by
      intro h1 h2 hmem1 hmem2
      exact CandidateHeapMatch.ready_heap_match_eval c h1 h2 n hready
        (hu h1 hmem1) (ht h2 hmem2))

theorem candidate_val_match_iff
    (c : SpecTec.context) (u t : SpecTec.valtype)
    (b : Bool) (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hu : InTableVal c u) (ht : InTableVal c t) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_valtype» c.TYPES u t⟩)
      start (.success (.of b)) finish ↔
    b = candidateValMatch c u t ∧ finish = start := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (candidate_val_match_total c u t start hready hu ht)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact candidate_val_match_total c u t finish hready hu ht

end properties.wasm_module_ok.CandidateValMatch
