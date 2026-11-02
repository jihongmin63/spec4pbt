import properties.wasm_module_ok.ConstExtendedCandidateReady
import properties.wasm_module_ok.CandidateTraceReady
import properties.wasm_module_ok.ConstCandidateTableMembership

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstTraceNestedReady

theorem nested_table_ready_of_types_eq
    (c d : SpecTec.context) (h : c.TYPES = d.TYPES) :
    CandidateNestedReady.nestedTableReady c =
      CandidateNestedReady.nestedTableReady d := by
  have hindexed : CandidateNestedReady.nestedIndexed c =
      CandidateNestedReady.nestedIndexed d := by
    funext ht
    simp [CandidateNestedReady.nestedIndexed, h]
  have hentry : CandidateNestedReady.nestedEntryReady c =
      CandidateNestedReady.nestedEntryReady d := by
    funext p
    simp [CandidateNestedReady.nestedEntryReady,
      h, hindexed]
  simp [CandidateNestedReady.nestedTableReady, h, hentry]

theorem trace_nested_ready_at
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8]) :
    CandidateNestedReady.nestedTableReady c = true := by
  have hvalidated : ValidatedTypeChain.ValidatedTypes tr.c0 :=
    ValidatedTypeChain.types_ok_preserves
      {tr.c with REFS := tr.free} tr.c0 m.TYPES tr.n2 tr.n3
      (CandidateTypesTraceIntegration.initial_validated m tr) tr.types_ok
  have hzero :=
    ConstExtendedCandidateReady.nested_table_ready_of_validated_types
      tr.c0 hvalidated
  rw [nested_table_ready_of_types_eq c tr.c0
    (CandidateTraceReady.trace_types_eq m tr c hc)]
  exact hzero

theorem trace_constant_instruction_types_in_table
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (start middle finish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt i⟩)
      middle (.success (.of iit)) finish) :
    (∀ t ∈ iit.1.INS.2, CandidateValMatch.InTableVal c t) ∧
      (∀ t ∈ iit.1.OUTS.2, CandidateValMatch.InTableVal c t) := by
  have hprov := CandidateTraceReady.trace_provenance_at m tr c hc
  exact ⟨ConstExtendedCandidateReady.is_const_instruction_inputs_in_table
      c irt i iit start middle finish hconst hcall hprov
      (trace_nested_ready_at m tr c hc),
    ConstCandidateTableMembership.is_const_instruction_outputs_in_table
      c irt i iit start middle finish hconst hcall hprov⟩

end properties.wasm_module_ok.ConstTraceNestedReady
