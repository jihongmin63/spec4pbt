import properties.wasm_module_ok.ConstStructImplicitProduction
import properties.wasm_module_ok.ConstStructExplicitProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStructOutputCover

theorem implicit_output_has_seed
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (u : SpecTec.valtype) (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«STRUCT.NEW» x .Implicit)⟩)
      start (.success (.of iit)) fin)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    ConstStructImplicitProduction.structImplicitSeed c u = true := by
  obtain ⟨ys, dt, middle, hstruct, hfields, hget, hiit⟩ :=
    (ConstStructImplicitDispatch.struct_new_implicit_constant_instruction_iff
      c irt x iit start fin).1 ⟨rfl, hcall⟩
  have hu : u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
    rw [hiit] at houts
    simpa using houts.symm
  obtain ⟨hstructResult, _⟩ :=
    (StructTypeDecision.struct_type_success_iff_result
      c x (.StructT ys) start middle).1 hstruct
  obtain ⟨hfieldsResult, _⟩ :=
    (StructImplicitFieldsDecision.fields_success_iff_defaultable
      ys middle fin).1 hfields
  exact (ConstStructImplicitProduction.struct_implicit_seed_iff c u).2
    ⟨x, dt, ys, hget, hstructResult, hfieldsResult, hu⟩

theorem explicit_output_has_step
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«STRUCT.NEW» x .Explicit)⟩)
      start (.success (.of iit)) fin)
    (hinputs : ∀ t ∈ iit.1.INS.2, t ∈ s)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    ConstStructExplicitProduction.structExplicitStep c s u = true := by
  obtain ⟨ys, ts, dt, middle, hstruct, hfields, hget, hiit⟩ :=
    (ConstStructExplicitDispatch.struct_new_explicit_constant_instruction_iff
      c irt x iit start fin).1 ⟨rfl, hcall⟩
  have hu : u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
    rw [hiit] at houts
    simpa using houts.symm
  have hts : ∀ t ∈ ts, t ∈ s := by
    rw [hiit] at hinputs
    simpa using hinputs
  obtain ⟨hstructResult, _⟩ :=
    (StructTypeDecision.struct_type_success_iff_result
      c x (.StructT ys) start middle).1 hstruct
  obtain ⟨hfieldsResult, _⟩ :=
    (StructExplicitFieldsDecision.fields_success_iff_inputs
      ys ts middle fin).1 hfields
  exact (ConstStructExplicitProduction.struct_explicit_step_iff c s u).2
    ⟨x, dt, ys, hget, hstructResult, hu,
      by simpa [← hfieldsResult] using hts⟩

end properties.wasm_module_ok.ConstStructOutputCover
