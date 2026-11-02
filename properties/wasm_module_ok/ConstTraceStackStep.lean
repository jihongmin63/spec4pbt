import properties.wasm_module_ok.ConstMatchAwareStackStep
import properties.wasm_module_ok.ConstTraceNestedReady

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstTraceStackStep

theorem trace_stack_entries_next_round
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (irt : SpecTec.inferresulttype) (i : SpecTec.instr)
    (iit : SpecTec.inferinstrtype)
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
    (hactual : ∀ t ∈ available,
      CandidateValMatch.InTableVal c t) :
    (∀ t ∈ pushed.2,
      t ∈ FiniteClosure.iterate
        (ConstMatchAwareClosure.matchAwareStep c) (round + 1)) ∧
    (∀ t ∈ pushed.2, CandidateValMatch.InTableVal c t) := by
  obtain ⟨hrequired, houtTable⟩ :=
    ConstTraceNestedReady.trace_constant_instruction_types_in_table
      m tr c hc irt i iit start middle instructionFinish hconst hcall
  have hready := CandidateTraceReady.trace_ready_at m tr c hc
  have hround := ConstMatchAwareStackStep.stack_entries_next_round
    c irt i iit available popped pushed u round
    start middle instructionFinish popStart popFinish pushFinish
    hconst hcall hpop hpush houts hstack hready hactual hrequired
  have hpush' : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$push» c (.NoEllipses, [u]) popped⟩)
      popFinish (.success (.of pushed)) pushFinish := by
    simpa only [houts] using hpush
  have htable := StackClosure.pop_push_entries_closed
    c iit.1.INS.2 [u] available popped pushed
    popStart popFinish pushFinish hpop hpush'
    (CandidateValMatch.InTableVal c) hactual
    (by
      intro t ht
      exact houtTable t (by simpa [houts] using ht))
  exact ⟨hround, htable⟩

end properties.wasm_module_ok.ConstTraceStackStep
