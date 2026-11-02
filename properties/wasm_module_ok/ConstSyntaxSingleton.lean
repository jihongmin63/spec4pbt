import properties.wasm_module_ok.ConstSyntaxCandidate

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstSyntaxSingleton

theorem syntax_instruction_singleton_outputs
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (start finish : Nat)
    (hsyntax : ConstAdditionalSyntaxValidation.Syntax c i)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt i⟩)
      start (.success (.of iit)) finish) :
    ∃ u : SpecTec.valtype, iit.1.OUTS = (.NoEllipses, [u]) := by
  cases hsyntax with
  | arithmetic i hi =>
    simp only [ConstArithmeticValidation.arithmeticOps,
      List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with heq | heq | heq | heq | heq | heq <;> subst i <;>
      obtain ⟨nt, _, heffect⟩ :=
        (ConstNumericBinopDispatch.numeric_binop_dispatch_iff
          c irt _ iit start finish).1 hcall <;>
      exact ⟨.NumT nt, by rw [heffect]⟩
  | num v =>
    obtain ⟨heffect, _⟩ :=
      ConstLiteralDispatch.const_literal_effect c irt v iit start finish hcall
    exact ⟨.NumT (ConstLiteralEffect.numericType v), by rw [heffect]⟩
  | vec v =>
    obtain ⟨heffect, _⟩ :=
      ConstVectorDispatch.vec_literal_effect c irt v iit start finish hcall
    exact ⟨.VecT .V128T, by rw [heffect]⟩
  | refNull ht =>
    obtain ⟨_, heffect, _⟩ :=
      (ConstRefNullDispatch.ref_null_dispatch_iff
        c irt ht iit start finish).1 hcall
    exact ⟨.RefT (.«% %» .Null ht), by rw [heffect]⟩
  | refFunc x =>
    obtain ⟨dt, _, _, heffect, _⟩ :=
      (ConstRefFuncEffect.ref_func_instruction_iff
        c irt x iit start finish).1 hcall
    exact ⟨.RefT (.«% %» .NoNull (.DefHT dt)), by rw [heffect]⟩
  | refI31 =>
    obtain ⟨heffect, _⟩ :=
      (ConstI31Dispatch.i31_instruction_effect
        c irt iit start finish hcall)
    exact ⟨.RefT (.«% %» .NoNull .I31HT), by rw [heffect]⟩
  | structNew x op =>
    cases op with
    | Implicit =>
      obtain ⟨_, dt, _, _, _, _, heffect⟩ :=
        (ConstStructImplicitDispatch.struct_new_implicit_dispatch_iff
          c irt x iit start finish).1 hcall
      exact ⟨.RefT (.«% %» .NoNull (.DefHT dt)), by rw [heffect]⟩
    | Explicit =>
      obtain ⟨_, _, dt, _, _, _, _, heffect⟩ :=
        (ConstStructExplicitDispatch.struct_new_explicit_dispatch_iff
          c irt x iit start finish).1 hcall
      exact ⟨.RefT (.«% %» .NoNull (.DefHT dt)), by rw [heffect]⟩
  | arrayNew x op =>
    cases op with
    | Implicit =>
      obtain ⟨_, _, dt, _, _, _, _, _, _, heffect⟩ :=
        (ConstArrayImplicitDispatch.array_new_implicit_dispatch_iff
          c irt x iit start finish).1 hcall
      exact ⟨.RefT (.«% %» .NoNull (.DefHT dt)), by rw [heffect]⟩
    | Explicit =>
      obtain ⟨_, _, dt, _, _, _, _, heffect⟩ :=
        (ConstArrayExplicitDispatch.array_new_explicit_dispatch_iff
          c irt x iit start finish).1 hcall
      exact ⟨.RefT (.«% %» .NoNull (.DefHT dt)), by rw [heffect]⟩
  | arrayNewFixed x count =>
    obtain ⟨_, _, dt, _, _, _, _, heffect⟩ :=
      (ConstArrayFixedDispatch.array_new_fixed_dispatch_iff
        c irt x count iit start finish).1 hcall
    exact ⟨.RefT (.«% %» .NoNull (.DefHT dt)), by rw [heffect]⟩
  | externConvert op =>
    obtain ⟨_, ht2, nu, _, _, _, _, heffect⟩ :=
      (ConstExternConvertDispatch.extern_convert_dispatch_iff
        c irt op iit start finish).1 hcall
    exact ⟨.RefT (.«% %» nu ht2), by rw [heffect]⟩
  | globalGet x t hget =>
    obtain ⟨_, actual, _, heffect, _⟩ :=
      (ConstGlobalGetDispatch.global_get_dispatch_iff
        c irt x iit start finish).1 hcall
    exact ⟨actual, by rw [heffect]⟩

theorem is_const_instruction_singleton_outputs
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
    ∃ u : SpecTec.valtype, iit.1.OUTS = (.NoEllipses, [u]) := by
  have hsyntax :=
    (ConstSyntaxClassification.is_const_success_iff
      c i start middle).1 hconst |>.1
  exact syntax_instruction_singleton_outputs
    c irt i iit middle finish hsyntax hcall

end properties.wasm_module_ok.ConstSyntaxSingleton
