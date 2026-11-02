import properties.wasm_module_ok.ConstArrayImplicitDispatch
import properties.wasm_module_ok.ConstArrayExplicitDispatch
import properties.wasm_module_ok.ConstArrayFixedDispatch
import properties.wasm_module_ok.ConstArrayFixedZeroProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArrayOutputSeed

theorem array_new_implicit_output_has_zero_seed
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW» x .Implicit)⟩)
      start (.success (.of iit)) fin) :
    ∃ dt : SpecTec.deftype,
      c.TYPES[x]? = some dt ∧
      ConstArrayFixedZeroProduction.arrayFixedZeroSeed c
        (.RefT (.«% %» .NoNull (.DefHT dt))) = true ∧
      iit.1.OUTS = (.NoEllipses,
        [.RefT (.«% %» .NoNull (.DefHT dt))]) := by
  obtain ⟨ft, t, dt, middle, finish, harray, _, _, hget, hiit⟩ :=
    (ConstArrayImplicitDispatch.array_new_implicit_dispatch_iff
      c irt x iit start fin).1 h
  have harrayResult :=
    (ArrayTypeDecision.array_type_success_iff_result
      c x (.ArrayT ft) start middle).1 harray |>.1
  refine ⟨dt, hget, ?_, ?_⟩
  · exact (ConstArrayFixedZeroProduction.array_fixed_zero_seed_iff
      c _).2 ⟨x, dt, ft, hget, harrayResult, rfl⟩
  · rw [hiit]

theorem array_new_explicit_output_has_zero_seed
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW» x .Explicit)⟩)
      start (.success (.of iit)) fin) :
    ∃ dt : SpecTec.deftype,
      c.TYPES[x]? = some dt ∧
      ConstArrayFixedZeroProduction.arrayFixedZeroSeed c
        (.RefT (.«% %» .NoNull (.DefHT dt))) = true ∧
      iit.1.OUTS = (.NoEllipses,
        [.RefT (.«% %» .NoNull (.DefHT dt))]) := by
  obtain ⟨ft, t, dt, middle, harray, _, hget, hiit⟩ :=
    (ConstArrayExplicitDispatch.array_new_explicit_dispatch_iff
      c irt x iit start fin).1 h
  have harrayResult :=
    (ArrayTypeDecision.array_type_success_iff_result
      c x (.ArrayT ft) start middle).1 harray |>.1
  refine ⟨dt, hget, ?_, ?_⟩
  · exact (ConstArrayFixedZeroProduction.array_fixed_zero_seed_iff
      c _).2 ⟨x, dt, ft, hget, harrayResult, rfl⟩
  · rw [hiit]

theorem array_new_fixed_output_has_zero_seed
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x count : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW_FIXED» x count)⟩)
      start (.success (.of iit)) fin) :
    ∃ dt : SpecTec.deftype,
      c.TYPES[x]? = some dt ∧
      ConstArrayFixedZeroProduction.arrayFixedZeroSeed c
        (.RefT (.«% %» .NoNull (.DefHT dt))) = true ∧
      iit.1.OUTS = (.NoEllipses,
        [.RefT (.«% %» .NoNull (.DefHT dt))]) := by
  obtain ⟨ft, t, dt, middle, harray, _, hget, hiit⟩ :=
    (ConstArrayFixedDispatch.array_new_fixed_dispatch_iff
      c irt x count iit start fin).1 h
  have harrayResult :=
    (ArrayTypeDecision.array_type_success_iff_result
      c x (.ArrayT ft) start middle).1 harray |>.1
  refine ⟨dt, hget, ?_, ?_⟩
  · exact (ConstArrayFixedZeroProduction.array_fixed_zero_seed_iff
      c _).2 ⟨x, dt, ft, hget, harrayResult, rfl⟩
  · rw [hiit]

theorem array_new_implicit_output_seed
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (u : SpecTec.valtype) (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW» x .Implicit)⟩)
      start (.success (.of iit)) fin)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    ConstArrayFixedZeroProduction.arrayFixedZeroSeed c u = true := by
  obtain ⟨dt, _, hseed, hout⟩ :=
    array_new_implicit_output_has_zero_seed c irt x iit start fin hcall
  have hu : u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
    rw [hout] at houts
    simpa using houts.symm
  simpa only [hu] using hseed

theorem array_new_explicit_output_seed
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (u : SpecTec.valtype) (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW» x .Explicit)⟩)
      start (.success (.of iit)) fin)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    ConstArrayFixedZeroProduction.arrayFixedZeroSeed c u = true := by
  obtain ⟨dt, _, hseed, hout⟩ :=
    array_new_explicit_output_has_zero_seed c irt x iit start fin hcall
  have hu : u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
    rw [hout] at houts
    simpa using houts.symm
  simpa only [hu] using hseed

theorem array_new_fixed_output_seed
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x count : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (u : SpecTec.valtype) (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW_FIXED» x count)⟩)
      start (.success (.of iit)) fin)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    ConstArrayFixedZeroProduction.arrayFixedZeroSeed c u = true := by
  obtain ⟨dt, _, hseed, hout⟩ :=
    array_new_fixed_output_has_zero_seed c irt x count iit start fin hcall
  have hu : u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
    rw [hout] at houts
    simpa using houts.symm
  simpa only [hu] using hseed

end properties.wasm_module_ok.ConstArrayOutputSeed
