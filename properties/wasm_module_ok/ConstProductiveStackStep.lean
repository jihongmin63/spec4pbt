import properties.wasm_module_ok.ConstProductiveClosure
import properties.wasm_module_ok.StackClosure

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstProductiveStackStep

/-- One successful constant instruction retains productive stack entries and
adds its actual singleton output in the next finite round. -/
theorem stack_entries_next_round
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (available : List SpecTec.valtype)
    (popped pushed : SpecTec.inferresulttype)
    (u : SpecTec.valtype) (round : Nat)
    (start middle instructionFinish popStart popFinish pushFinish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt i⟩)
      middle (.success (.of iit)) instructionFinish)
    (hpop : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (.NoEllipses, iit.1.INS.2) (.NoEllipses, available)⟩)
      popStart (.success (.of popped)) popFinish)
    (hpush : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$push» c iit.1.OUTS popped⟩)
      popFinish (.success (.of pushed)) pushFinish)
    (houts : iit.1.OUTS = (.NoEllipses, [u]))
    (hstack : ∀ t ∈ available,
      t ∈ FiniteClosure.iterate (ConstProductiveClosure.productiveStep c) round)
    (hready : CandidateTypeReady.Ready c)
    (hactual : ∀ actual ∈ available,
      CandidateValMatch.InTableVal c actual)
    (hrequired : ∀ required ∈ iit.1.INS.2,
      CandidateValMatch.InTableVal c required) :
    ∀ t ∈ pushed.2,
      t ∈ FiniteClosure.iterate
        (ConstProductiveClosure.productiveStep c) (round + 1) := by
  let s := FiniteClosure.iterate
    (ConstProductiveClosure.productiveStep c) round
  have hbounded : s ⊆ FiniteValidTypes.candidateUniverse c :=
    FiniteClosure.iterate_bounded
      (FiniteValidTypes.candidateUniverse c)
      (ConstProductiveClosure.productiveStep c)
      (ConstProductiveClosure.productive_step_bounded c) round
  have houtput : u ∈ ConstProductiveClosure.productiveStep c s :=
    ConstProductiveClosure.output_mem_productive_step
      c irt i iit available popped s u
      start middle instructionFinish popStart popFinish
      hconst hcall hpop hbounded hstack hready hactual hrequired houts
  have hretain : ∀ t ∈ available,
      t ∈ ConstProductiveClosure.productiveStep c s := by
    intro t ht
    exact ConstProductiveClosure.productive_step_inflate c s
      (hstack t ht)
  have hpush' : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$push» c (.NoEllipses, [u]) popped⟩)
      popFinish (.success (.of pushed)) pushFinish := by
    simpa only [houts] using hpush
  have hclosed := StackClosure.pop_push_entries_closed
    c iit.1.INS.2 [u] available popped pushed
    popStart popFinish pushFinish hpop hpush'
    (fun t => t ∈ ConstProductiveClosure.productiveStep c s)
    hretain (by
      intro t ht
      simp only [List.mem_singleton] at ht
      subst t
      exact houtput)
  change ∀ t ∈ pushed.2,
    t ∈ ConstProductiveClosure.productiveStep c s
  exact hclosed

end properties.wasm_module_ok.ConstProductiveStackStep
