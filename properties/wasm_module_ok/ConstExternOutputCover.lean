import properties.wasm_module_ok.ConstExternConvertProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExternOutputCover

theorem extern_output_has_step
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.externop_) (iit : SpecTec.inferinstrtype)
    (s : Finset SpecTec.valtype) (t u : SpecTec.valtype)
    (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«EXTERN.CONVERT» op)⟩)
      start (.success (.of iit)) fin)
    (hinputs : iit.1.INS = (.NoEllipses, [t]))
    (hinput : t ∈ s)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    ConstExternConvertProduction.externTypeStep s u = true := by
  obtain ⟨hresult, _⟩ :=
    (ConstExternConvertDecision.extern_convert_success_iff_result
      c irt op iit start fin).1 hcall
  cases href : PeekRefDecision.peekRefResult
      (PeekDecision.peekResult 0 irt) with
  | none =>
    simp [ConstExternConvertDecision.externConvertResult, href] at hresult
  | some rt =>
    cases rt with
    | «% %» nu ht =>
      have hiit : iit =
          ConstExternConvertProduction.externInstrType nu op := by
        simpa [ConstExternConvertDecision.externConvertResult, href,
          ConstExternConvertProduction.externInstrType,
          ConstExternConvertProduction.externInput,
          ConstExternConvertProduction.externOutput] using hresult.symm
      have ht : t = ConstExternConvertProduction.externInput nu op := by
        rw [hiit] at hinputs
        simpa [ConstExternConvertProduction.externInstrType] using hinputs.symm
      have hu : u = ConstExternConvertProduction.externOutput nu op := by
        rw [hiit] at houts
        simpa [ConstExternConvertProduction.externInstrType] using houts.symm
      exact (ConstExternConvertProduction.extern_type_step_iff s u).2
        ⟨nu, op, by simpa only [ht] using hinput, hu⟩

theorem extern_output_has_step_of_all_inputs
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.externop_) (iit : SpecTec.inferinstrtype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«EXTERN.CONVERT» op)⟩)
      start (.success (.of iit)) fin)
    (hinputs : ∀ t ∈ iit.1.INS.2, t ∈ s)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    ConstExternConvertProduction.externTypeStep s u = true := by
  obtain ⟨hresult, _⟩ :=
    (ConstExternConvertDecision.extern_convert_success_iff_result
      c irt op iit start fin).1 hcall
  cases href : PeekRefDecision.peekRefResult
      (PeekDecision.peekResult 0 irt) with
  | none =>
    simp [ConstExternConvertDecision.externConvertResult, href] at hresult
  | some rt =>
    cases rt with
    | «% %» nu ht =>
      have hiit : iit =
          ConstExternConvertProduction.externInstrType nu op := by
        simpa [ConstExternConvertDecision.externConvertResult, href,
          ConstExternConvertProduction.externInstrType,
          ConstExternConvertProduction.externInput,
          ConstExternConvertProduction.externOutput] using hresult.symm
      apply extern_output_has_step c irt op iit s
        (ConstExternConvertProduction.externInput nu op) u start fin hcall
      · rw [hiit]
        rfl
      · apply hinputs
        rw [hiit]
        simp [ConstExternConvertProduction.externInstrType]
      · exact houts

end properties.wasm_module_ok.ConstExternOutputCover
