import properties.wasm_module_ok.ConstStaticAgreement
import properties.wasm_module_ok.ConstTraceStackStep
import properties.wasm_module_ok.ConstSyntaxSingleton

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStaticStackStep

/-- One constant instruction advances the stack invariant even after any
number of successful local initializations. -/
theorem static_stack_entries_next_round
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (origin current : SpecTec.context)
    (horigin : origin ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (hstatic : ConstStaticAgreement.StaticAgreement origin current)
    (irt : SpecTec.inferresulttype) (i : SpecTec.instr)
    (iit : SpecTec.inferinstrtype)
    (available : List SpecTec.valtype)
    (popped pushed : SpecTec.inferresulttype)
    (round : Nat)
    (start middle instructionFinish popStart popFinish pushFinish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» current i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok current irt i⟩)
      middle (.success (.of iit)) instructionFinish)
    (hpop : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» current
          (.NoEllipses, iit.1.INS.2) (.NoEllipses, available)⟩)
      popStart (.success (.of popped)) popFinish)
    (hpush : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$push» current iit.1.OUTS popped⟩)
      popFinish (.success (.of pushed)) pushFinish)
    (hstack : ∀ t ∈ available,
      t ∈ FiniteClosure.iterate
        (ConstMatchAwareClosure.matchAwareStep origin) round)
    (hactual : ∀ t ∈ available,
      CandidateValMatch.InTableVal origin t) :
    (∀ t ∈ pushed.2,
      t ∈ FiniteClosure.iterate
        (ConstMatchAwareClosure.matchAwareStep origin) (round + 1)) ∧
    (∀ t ∈ pushed.2, CandidateValMatch.InTableVal origin t) := by
  obtain ⟨u, houts⟩ :=
    ConstSyntaxSingleton.is_const_instruction_singleton_outputs
      current irt i iit start middle instructionFinish hconst hcall
  have hready := ConstStaticAgreement.ready origin current hstatic
    (CandidateTraceReady.trace_ready_at m tr origin horigin)
  have hprov := ConstStaticAgreement.provenance origin current hstatic
    (CandidateTraceReady.trace_provenance_at m tr origin horigin)
  have hnested := ConstStaticAgreement.nested_table_ready
    origin current hstatic
    (ConstTraceNestedReady.trace_nested_ready_at m tr origin horigin)
  have hrequired :=
    ConstExtendedCandidateReady.is_const_instruction_inputs_in_table
      current irt i iit start middle instructionFinish
      hconst hcall hprov hnested
  have houtTable :=
    ConstCandidateTableMembership.is_const_instruction_outputs_in_table
      current irt i iit start middle instructionFinish
      hconst hcall hprov
  have hstackCurrent : ∀ t ∈ available,
      t ∈ FiniteClosure.iterate
        (ConstMatchAwareClosure.matchAwareStep current) round := by
    intro t ht
    rw [← ConstStaticAgreement.closure_iterate
      origin current hstatic round]
    exact hstack t ht
  have hactualCurrent : ∀ t ∈ available,
      CandidateValMatch.InTableVal current t := by
    intro t ht
    exact ConstStaticAgreement.in_table_val
      origin current hstatic t (hactual t ht)
  have hclosed := ConstMatchAwareStackStep.stack_entries_next_round
    current irt i iit available popped pushed u round
    start middle instructionFinish popStart popFinish pushFinish
    hconst hcall hpop hpush houts hstackCurrent hready
      hactualCurrent hrequired
  have hpush' : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$push» current (.NoEllipses, [u]) popped⟩)
      popFinish (.success (.of pushed)) pushFinish := by
    simpa only [houts] using hpush
  have htable := StackClosure.pop_push_entries_closed
    current iit.1.INS.2 [u] available popped pushed
    popStart popFinish pushFinish hpop hpush'
    (CandidateValMatch.InTableVal current) hactualCurrent
    (by
      intro t ht
      exact houtTable t (by simpa [houts] using ht))
  constructor
  · intro t ht
    rw [ConstStaticAgreement.closure_iterate
      origin current hstatic (round + 1)]
    exact hclosed t ht
  · intro t ht
    exact CandidateProvenanceSteps.in_table_val_of_types_eq
      current origin t hstatic.types.symm (htable t ht)

end properties.wasm_module_ok.ConstStaticStackStep
