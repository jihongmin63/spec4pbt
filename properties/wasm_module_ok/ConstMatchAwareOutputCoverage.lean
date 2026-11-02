import properties.wasm_module_ok.ConstExtendedMatchSaturation
import properties.wasm_module_ok.ConstClosureOutputCoverage

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstMatchAwareOutputCoverage

/-- One translated constant instruction whose actual pop succeeds contributes
its output to the finite closure after saturating earlier source types by the
translated value-type match. -/
theorem output_mem_match_aware_step
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (available sources : List SpecTec.valtype)
    (result : SpecTec.inferresulttype)
    (u : SpecTec.valtype)
    (start middle instructionFinish popStart popFinish : Nat)
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
      popStart (.success (.of result)) popFinish)
    (hready : CandidateTypeReady.Ready c)
    (hsource : ∀ actual ∈ available, actual ∈ sources)
    (hactual : ∀ actual ∈ available,
      CandidateValMatch.InTableVal c actual)
    (hrequired : ∀ required ∈ iit.1.INS.2,
      CandidateValMatch.InTableVal c required)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    u ∈ ConstExternConvertClosure.externClosureStep c
      (ConstExtendedMatchSaturation.extendedMatchSaturation c sources) := by
  have hinputs :=
    ConstExtendedMatchSaturation.const_pop_inputs_in_extended_saturation
      c irt i iit available sources result
      start middle instructionFinish popStart popFinish
      hconst hcall hpop hready hsource hactual hrequired
  exact ConstClosureOutputCoverage.step_of_is_const
    c irt (ConstExtendedMatchSaturation.extendedMatchSaturation c sources)
    i iit u start middle instructionFinish hconst hcall hinputs houts

end properties.wasm_module_ok.ConstMatchAwareOutputCoverage
