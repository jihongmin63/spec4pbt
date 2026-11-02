import properties.wasm_module_ok.ConstClosureStatic
import properties.wasm_module_ok.ConstTraceStackStep
import properties.wasm_module_ok.ConstSyntaxSingleton

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstLocalStackStep

/-- A constant instruction in a locally initialized context advances the
closure of its originating module stage context. The stack invariant has no
height bound. -/
theorem local_stack_entries_next_round
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c d : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (indices : List SpecTec.idx) (initStart initFinish : Nat)
    (hinit : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c indices⟩)
      initStart (.success (.of d)) initFinish)
    (irt : SpecTec.inferresulttype) (i : SpecTec.instr)
    (iit : SpecTec.inferinstrtype)
    (available : List SpecTec.valtype)
    (popped pushed : SpecTec.inferresulttype)
    (round : Nat)
    (start middle instructionFinish popStart popFinish pushFinish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» d i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok d irt i⟩)
      middle (.success (.of iit)) instructionFinish)
    (hpop : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» d
          (.NoEllipses, iit.1.INS.2) (.NoEllipses, available)⟩)
      popStart (.success (.of popped)) popFinish)
    (hpush : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$push» d iit.1.OUTS popped⟩)
      popFinish (.success (.of pushed)) pushFinish)
    (hstack : ∀ t ∈ available,
      t ∈ FiniteClosure.iterate
        (ConstMatchAwareClosure.matchAwareStep c) round)
    (hactual : ∀ t ∈ available,
      CandidateValMatch.InTableVal c t) :
    (∀ t ∈ pushed.2,
      t ∈ FiniteClosure.iterate
        (ConstMatchAwareClosure.matchAwareStep c) (round + 1)) ∧
    (∀ t ∈ pushed.2, CandidateValMatch.InTableVal c t) := by
  obtain ⟨u, houts⟩ :=
    ConstSyntaxSingleton.is_const_instruction_singleton_outputs
      d irt i iit start middle instructionFinish hconst hcall
  have hready := ConstMatchReadyStatic.init_locals_ready
    c d indices initStart initFinish hinit
    (CandidateTraceReady.trace_ready_at m tr c hc)
  have hprov := ConstLocalContextReady.init_locals_provenance
    c d indices initStart initFinish hinit
    (CandidateTraceReady.trace_provenance_at m tr c hc)
  have hnested := ConstLocalContextReady.init_locals_nested_table_ready
    c d indices initStart initFinish hinit
    (ConstTraceNestedReady.trace_nested_ready_at m tr c hc)
  have hrequired :=
    ConstExtendedCandidateReady.is_const_instruction_inputs_in_table
      d irt i iit start middle instructionFinish
      hconst hcall hprov hnested
  have houtTable :=
    ConstCandidateTableMembership.is_const_instruction_outputs_in_table
      d irt i iit start middle instructionFinish
      hconst hcall hprov
  have hstackD : ∀ t ∈ available,
      t ∈ FiniteClosure.iterate
        (ConstMatchAwareClosure.matchAwareStep d) round := by
    intro t ht
    rw [← ConstClosureStatic.init_locals_closure_iterate
      c d indices initStart initFinish round hinit]
    exact hstack t ht
  have hactualD : ∀ t ∈ available,
      CandidateValMatch.InTableVal d t := by
    intro t ht
    exact ConstMatchReadyStatic.init_locals_in_table_val
      c d indices initStart initFinish hinit t (hactual t ht)
  have hclosed := ConstMatchAwareStackStep.stack_entries_next_round
    d irt i iit available popped pushed u round
    start middle instructionFinish popStart popFinish pushFinish
    hconst hcall hpop hpush houts hstackD hready hactualD hrequired
  have hpush' : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$push» d (.NoEllipses, [u]) popped⟩)
      popFinish (.success (.of pushed)) pushFinish := by
    simpa only [houts] using hpush
  have htable := StackClosure.pop_push_entries_closed
    d iit.1.INS.2 [u] available popped pushed
    popStart popFinish pushFinish hpop hpush'
    (CandidateValMatch.InTableVal d) hactualD
    (by
      intro t ht
      exact houtTable t (by simpa [houts] using ht))
  constructor
  · intro t ht
    rw [ConstClosureStatic.init_locals_closure_iterate
      c d indices initStart initFinish (round + 1) hinit]
    exact hclosed t ht
  · intro t ht
    have htypes := (LocalInitStatic.init_locals_static_fields
      c d indices initStart initFinish hinit).1
    exact CandidateProvenanceSteps.in_table_val_of_types_eq
      d c t htypes.symm (htable t ht)

end properties.wasm_module_ok.ConstLocalStackStep
