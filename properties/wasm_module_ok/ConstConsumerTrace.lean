import properties.wasm_module_ok.ConstConstructiveTrace
import properties.wasm_module_ok.PopGeneralValidation
import properties.wasm_module_ok.PushValidation
import properties.wasm_module_ok.LocalInitValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstConsumerTrace

/-- Append a singleton-output consumer using the exact translated stack
matching call. The producer's ending context and supply are retained. -/
theorem trace_snoc_of_match
    {origin current : SpecTec.context}
    {initial : SpecTec.inferresulttype}
    {xs : List SpecTec.instr}
    {start middle afterInstr afterMatch : Nat}
    (available required : List SpecTec.valtype)
    (u : SpecTec.valtype) (i : SpecTec.instr)
    (htrace : ConstConstructiveTrace.Trace origin initial xs current
      (.NoEllipses, available) start middle)
    (hinstr : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok current (.NoEllipses, available) i⟩)
      middle (.success (.of
        (⟨{ INS := (.NoEllipses, required),
             OUTS := (.NoEllipses, [u]) },
           ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) afterInstr)
    (hlen : required.length ≤ available.length)
    (hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype current
        (available.drop (available.length - required.length)) required⟩)
      afterInstr (.success (.of ())) afterMatch) :
    ConstConstructiveTrace.Trace origin initial (xs ++ [i]) current
      (.NoEllipses,
        available.take (available.length - required.length) ++ [u])
      start afterMatch := by
  apply ConstConstructiveTrace.trace_snoc htrace hinstr
    (LocalInitValidation.init_locals_nil_total current afterInstr)
    (PopGeneralValidation.pop_noellipses_of_match current
      required available afterInstr afterMatch hlen hmatch)
  simpa [PushValidation.pushOutcome, PushValidation.pushResult] using
    (PushValidation.push_total current (.NoEllipses, [u])
      (.NoEllipses, available.take
        (available.length - required.length)) afterMatch)

/-- Consume exactly the operands produced after an arbitrary older stack. -/
theorem trace_snoc_after_operands
    {origin current : SpecTec.context}
    {initial : SpecTec.inferresulttype}
    {xs : List SpecTec.instr}
    {start n : Nat}
    (stack actual required : List SpecTec.valtype)
    (u : SpecTec.valtype) (i : SpecTec.instr)
    (htrace : ConstConstructiveTrace.Trace origin initial xs current
      (.NoEllipses, stack ++ actual) start n)
    (hinstr : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok current (.NoEllipses, stack ++ actual) i⟩)
      n (.success (.of
        (⟨{ INS := (.NoEllipses, required),
             OUTS := (.NoEllipses, [u]) },
           ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n)
    (hlength : required.length = actual.length)
    (hmatch : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype current
        actual required⟩)
      n (.success (.of ())) n) :
    ConstConstructiveTrace.Trace origin initial (xs ++ [i]) current
      (.NoEllipses, stack ++ [u]) start n := by
  have hdrop : (stack ++ actual).drop
      ((stack ++ actual).length - required.length) = actual := by
    rw [hlength]
    simp
  have htake : (stack ++ actual).take
      ((stack ++ actual).length - required.length) = stack := by
    rw [hlength]
    simp
  have hmatch' : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype current
        ((stack ++ actual).drop
          ((stack ++ actual).length - required.length)) required⟩)
      n (.success (.of ())) n := by
    rw [hdrop]
    exact hmatch
  have hconsumer := trace_snoc_of_match
    (stack ++ actual) required u i htrace hinstr
      (by simp [hlength])
      hmatch'
  rw [htake] at hconsumer
  exact hconsumer

end properties.wasm_module_ok.ConstConsumerTrace
