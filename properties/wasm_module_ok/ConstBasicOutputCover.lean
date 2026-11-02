import properties.wasm_module_ok.ConstBasicSeed

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstBasicOutputCover

theorem numeric_output_in_basic
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.num_) (iit : SpecTec.inferinstrtype)
    (u : SpecTec.valtype) (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.CONST v)⟩)
      start (.success (.of iit)) fin)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    u ∈ ConstBasicSeed.basicBase c := by
  obtain ⟨hiit, _⟩ :=
    ConstLiteralDispatch.const_literal_effect c irt v iit start fin hcall
  have hu : u = .NumT (ConstLiteralEffect.numericType v) := by
    rw [hiit] at houts
    simpa using houts.symm
  subst u
  exact Finset.mem_union_left _
    (Finset.mem_union_left _
      (Finset.mem_union_left _
        ((ConstLiteralProduction.literal_base_mem_iff c _).2 (by rfl))))

theorem ref_null_output_in_basic
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (ht : SpecTec.heaptype) (iit : SpecTec.inferinstrtype)
    (u : SpecTec.valtype) (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«REF.NULL» ht)⟩)
      start (.success (.of iit)) fin)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    u ∈ ConstBasicSeed.basicBase c := by
  obtain ⟨hvalid, hiit, _⟩ :=
    (ConstRefNullDispatch.ref_null_dispatch_iff
      c irt ht iit start fin).1 hcall
  have hu : u = .RefT (.«% %» .Null ht) := by
    rw [hiit] at houts
    simpa using houts.symm
  subst u
  exact Finset.mem_union_left _
    (Finset.mem_union_left _
      (Finset.mem_union_right _
        ((ConstRefNullProduction.ref_null_base_mem_iff c _).2 hvalid)))

theorem ref_func_output_in_basic
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (iit : SpecTec.inferinstrtype)
    (u : SpecTec.valtype) (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«REF.FUNC» x)⟩)
      start (.success (.of iit)) fin)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    u ∈ ConstBasicSeed.basicBase c := by
  obtain ⟨dt, hget, href, hiit, _⟩ :=
    (ConstRefFuncCombined.ref_func_constant_instruction_iff
      c irt x iit start fin).1 ⟨rfl, hcall⟩
  have hu : u = .RefT (.«% %» .NoNull (.DefHT dt)) := by
    rw [hiit] at houts
    simpa using houts.symm
  subst u
  exact Finset.mem_union_left _
    (Finset.mem_union_right _
      ((ConstRefFuncProduction.ref_func_base_mem_iff c _).2
        ((ConstRefFuncProduction.ref_func_seed_iff c _).2
          ⟨x, dt, hget, href, rfl⟩)))

theorem global_get_output_in_basic
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.globalidx) (iit : SpecTec.inferinstrtype)
    (u : SpecTec.valtype) (start fin : Nat)
    (hsyntax : ConstSyntaxDecision.syntaxAllowed c (.«GLOBAL.GET» x) = true)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«GLOBAL.GET» x)⟩)
      start (.success (.of iit)) fin)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    u ∈ ConstBasicSeed.basicBase c := by
  obtain ⟨t, hget, hiit, _⟩ :=
    (ConstGlobalGetCombined.global_get_constant_instruction_iff
      c irt x iit start fin).1 ⟨hsyntax, hcall⟩
  have hu : u = t := by
    rw [hiit] at houts
    simpa using houts.symm
  subst u
  exact Finset.mem_union_right _
    ((ConstGlobalGetProduction.global_get_base_mem_iff c _).2
      ((ConstGlobalGetProduction.global_get_seed_iff c _).2
        ⟨x, t, hget, rfl⟩))

end properties.wasm_module_ok.ConstBasicOutputCover
