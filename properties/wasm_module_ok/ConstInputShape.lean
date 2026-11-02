import properties.wasm_module_ok.ConstSyntaxCandidate
import properties.wasm_module_ok.ConstSyntaxClassification

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstInputShape

/-- Every translated constant-eligible instruction has a concrete input
list, so the no-ellipses pop theorem applies to its actual effect. -/
theorem is_const_instruction_noellipses_inputs
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (start middle finish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt i⟩)
      middle (.success (.of iit)) finish) :
    iit.1.INS = (.NoEllipses, iit.1.INS.2) := by
  have hsyntax :=
    (ConstSyntaxClassification.is_const_success_iff
      c i start middle).1 hconst |>.1
  obtain ⟨need, _, hins, _, _⟩ :=
    ConstSyntaxCandidate.syntax_instruction_effect_candidate
      c c i irt iit middle finish hsyntax hcall
  rw [hins]

end properties.wasm_module_ok.ConstInputShape
