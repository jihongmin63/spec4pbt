import properties.wasm_module_ok.CandidateUniverseReady
import properties.wasm_module_ok.ConstSyntaxCandidate

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstCandidateTableMembership

/-- Under established context provenance, every output of a successful
constant-eligible instruction is backed by the matcher table. -/
theorem constant_instruction_outputs_in_table
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (start finish : Nat)
    (hsyntax : ConstAdditionalSyntaxValidation.Syntax c i)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt i⟩)
      start (.success (.of iit)) finish)
    (hprov : CandidateUniverseReady.Provenance c) :
    ∀ t ∈ iit.1.OUTS.2, CandidateValMatch.InTableVal c t := by
  obtain ⟨_, outs, _, hout, hcandidate⟩ :=
    ConstSyntaxCandidate.syntax_instruction_effect_candidate
      c c i irt iit start finish hsyntax hcall
  intro t ht
  rw [hout] at ht
  exact CandidateUniverseReady.candidate_universe_in_table
    c t hprov (hcandidate t ht)

theorem is_const_instruction_outputs_in_table
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (start middle finish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt i⟩)
      middle (.success (.of iit)) finish)
    (hprov : CandidateUniverseReady.Provenance c) :
    ∀ t ∈ iit.1.OUTS.2, CandidateValMatch.InTableVal c t := by
  have hsyntax :=
    (ConstSyntaxClassification.is_const_success_iff
      c i start middle).1 hconst |>.1
  exact constant_instruction_outputs_in_table c irt i iit
    middle finish hsyntax hcall hprov

end properties.wasm_module_ok.ConstCandidateTableMembership
