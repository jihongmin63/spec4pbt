import properties.wasm_module_ok.CandidateValMatch
import properties.wasm_module_ok.MatchReftypeLocal

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateReftypeMatch

/-- The exact executable reference matcher on values backed by the ready type
table. -/
def candidateReftypeMatch (c : SpecTec.context)
    (source target : SpecTec.reftype) : Bool :=
  MatchReftypeConditional.matchReftypeResult
    (fun h1 h2 =>
      (ReadyHeapMatch.readyHeapMatch c h1 h2).getD false)
    source target

theorem candidate_reftype_match_total
    (c : SpecTec.context) (source target : SpecTec.reftype)
    (n : Nat) (hready : CandidateTypeReady.Ready c)
    (hsource : CandidateValMatch.InTableVal c (.RefT source))
    (htarget : CandidateValMatch.InTableVal c (.RefT target)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_reftype»
        c.TYPES source target⟩)
      n (.success (.of (candidateReftypeMatch c source target))) n := by
  cases source with
  | «% %» null1 heap1 =>
    cases target with
    | «% %» null2 heap2 =>
      exact MatchReftypeLocal.match_reftype_pair_total
        c.TYPES
        (fun h1 h2 => (ReadyHeapMatch.readyHeapMatch c h1 h2).getD false)
        null1 null2 heap1 heap2 n
        (CandidateHeapMatch.ready_heap_match_eval c heap1 heap2 n hready
          (hsource heap1 (by simp [ReadyMatchReachability.sourceValHeaptypes]))
          (htarget heap2 (by simp [ReadyMatchReachability.sourceValHeaptypes])))

theorem candidate_reftype_match_iff
    (c : SpecTec.context) (source target : SpecTec.reftype)
    (b : Bool) (start finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (hsource : CandidateValMatch.InTableVal c (.RefT source))
    (htarget : CandidateValMatch.InTableVal c (.RefT target)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_reftype»
        c.TYPES source target⟩)
      start (.success (.of b)) finish ↔
    b = candidateReftypeMatch c source target ∧ finish = start := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h
        (candidate_reftype_match_total c source target start
          hready hsource htarget)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact candidate_reftype_match_total c source target finish
      hready hsource htarget

end properties.wasm_module_ok.CandidateReftypeMatch
