import properties.wasm_module_ok.ConstructiveBodyMatchers
import properties.wasm_module_ok.MatchReftypeLocal
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceMatcher
open SpecTec properties.wasm_module_ok

def refMatch (c : context) : reftype → reftype → Bool :=
  MatchReftypeConditional.matchReftypeResult (fun h1 h2 => (ReadyHeapMatch.readyHeapMatch c h1 h2).getD false)

theorem total (c : context) (r1 r2 : reftype) (n : Nat)
    (hr : CandidateTypeReady.Ready c)
    (h1 : CandidateValMatch.InTableVal c (.RefT r1))
    (h2 : CandidateValMatch.InTableVal c (.RefT r2)) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,Call.«$match_reftype» c.TYPES r1 r2⟩)
      n (.success (.of (refMatch c r1 r2))) n := by
  cases r1 with | «% %» n1 heap1 =>
   cases r2 with | «% %» n2 heap2 =>
    exact MatchReftypeLocal.match_reftype_pair_total c.TYPES _ n1 n2 heap1 heap2 n
      (CandidateHeapMatch.ready_heap_match_eval c heap1 heap2 n hr
        (h1 heap1 (by simp [ReadyMatchReachability.sourceValHeaptypes]))
        (h2 heap2 (by simp [ReadyMatchReachability.sourceValHeaptypes])))

theorem exact_call (c : context) (r1 r2 : reftype) (value : Bool) (start finish : Nat)
    (hr : CandidateTypeReady.Ready c)
    (h1 : CandidateValMatch.InTableVal c (.RefT r1))
    (h2 : CandidateValMatch.InTableVal c (.RefT r2)) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,Call.«$match_reftype» c.TYPES r1 r2⟩)
      start (.success (.of value)) finish ↔ value=refMatch c r1 r2 ∧ finish=start := by
  constructor
  · intro h
    obtain ⟨he,hf⟩ := properties.wasm_module_ok.Execution.eval_deterministic h (total c r1 r2 start hr h1 h2)
    cases he
    exact ⟨rfl,hf⟩
  · rintro ⟨rfl,rfl⟩
    exact total c r1 r2 finish hr h1 h2

theorem base_backed (c : context) (nu : SpecTec.null) (heap : heaptype)
    (hb : heap∈HeaptypeValidation.baseHeaptypes) :
    CandidateValMatch.InTableVal c (.RefT (.«% %» nu heap)) := by
  intro h hh
  have he : h=heap := by simpa [ReadyMatchReachability.sourceValHeaptypes] using hh
  subst h
  exact .base heap hb

#print axioms exact_call
end properties.wasm_module_ok.ConstructiveBodyReferenceMatcher
