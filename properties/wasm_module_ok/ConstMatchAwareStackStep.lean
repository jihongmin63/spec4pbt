import properties.wasm_module_ok.ConstMatchAwareClosure
import properties.wasm_module_ok.StackClosure

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstMatchAwareStackStep

/-- One successful constant instruction preserves the finite closure
invariant on every retained stack entry and adds its singleton output. -/
theorem stack_entries_next_round
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (available : List SpecTec.valtype)
    (popped pushed : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (round : Nat)
    (start middle instructionFinish popStart popFinish pushFinish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt i⟩)
      middle (.success (.of iit)) instructionFinish)
    (hpop : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, iit.1.INS.2) (.NoEllipses, available)⟩)
      popStart (.success (.of popped)) popFinish)
    (hpush : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$push» c iit.1.OUTS popped⟩)
      popFinish (.success (.of pushed)) pushFinish)
    (houts : iit.1.OUTS = (.NoEllipses, [u]))
    (hstack : ∀ t ∈ available,
      t ∈ FiniteClosure.iterate (ConstMatchAwareClosure.matchAwareStep c) round)
    (hready : CandidateTypeReady.Ready c)
    (hactual : ∀ actual ∈ available,
      CandidateValMatch.InTableVal c actual)
    (hrequired : ∀ required ∈ iit.1.INS.2,
      CandidateValMatch.InTableVal c required) :
    ∀ t ∈ pushed.2,
      t ∈ FiniteClosure.iterate
        (ConstMatchAwareClosure.matchAwareStep c) (round + 1) := by
  let s := FiniteClosure.iterate
    (ConstMatchAwareClosure.matchAwareStep c) round
  have hbounded : s ⊆ FiniteValidTypes.candidateUniverse c :=
    FiniteClosure.iterate_bounded
      (FiniteValidTypes.candidateUniverse c)
      (ConstMatchAwareClosure.matchAwareStep c)
      (ConstMatchAwareClosure.match_aware_step_bounded c) round
  have houtput : u ∈ ConstMatchAwareClosure.matchAwareStep c s :=
    ConstMatchAwareClosure.output_mem_match_aware_step
      c irt i iit available popped s u
      start middle instructionFinish popStart popFinish
      hconst hcall hpop hbounded hstack hready hactual hrequired houts
  have hretain : ∀ t ∈ available,
      t ∈ ConstMatchAwareClosure.matchAwareStep c s := by
    intro t ht
    exact ConstMatchAwareClosure.match_aware_step_inflate c s
      (hstack t ht)
  have hpush' : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$push» c (.NoEllipses, [u]) popped⟩)
      popFinish (.success (.of pushed)) pushFinish := by
    simpa only [houts] using hpush
  have hclosed := StackClosure.pop_push_entries_closed
    c iit.1.INS.2 [u] available popped pushed
    popStart popFinish pushFinish hpop hpush'
    (fun t => t ∈ ConstMatchAwareClosure.matchAwareStep c s)
    hretain (by
      intro t ht
      simp only [List.mem_singleton] at ht
      subst t
      exact houtput)
  change ∀ t ∈ pushed.2,
    t ∈ ConstMatchAwareClosure.matchAwareStep c s
  exact hclosed

end properties.wasm_module_ok.ConstMatchAwareStackStep
