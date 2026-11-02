import properties.wasm_module_ok.ConstArithmeticOutputCover
import properties.wasm_module_ok.ConstI31Production
import properties.wasm_module_ok.ConstExternConvertProduction

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstBasicInputCandidate

theorem binop_inputs_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.binop_) (iit : SpecTec.inferinstrtype)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.BINOP op)⟩)
      start (.success (.of iit)) finish) :
    ∀ t ∈ iit.1.INS.2,
      t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨nt, _, rfl⟩ :=
    (ConstNumericBinopDispatch.numeric_binop_dispatch_iff
      c irt op iit start finish).1 hcall
  intro t ht
  have hnum : ValtypeValidation.valtypeValid c (.NumT nt) = true := by
    cases nt <;> rfl
  have hcandidate :=
    FiniteValidTypes.valid_mem_candidateUniverse c (.NumT nt) hnum
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with heq | heq <;> cases heq <;> exact hcandidate

theorem vec_const_inputs_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.vec_) (iit : SpecTec.inferinstrtype)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«VEC.CONST» v)⟩)
      start (.success (.of iit)) finish) :
    ∀ t ∈ iit.1.INS.2,
      t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨rfl, _⟩ :=
    ConstVectorDispatch.vec_literal_effect c irt v iit start finish hcall
  simp

theorem ref_i31_inputs_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (iit : SpecTec.inferinstrtype) (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt .«REF.I31»⟩)
      start (.success (.of iit)) finish) :
    ∀ t ∈ iit.1.INS.2,
      t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨rfl, _⟩ :=
    ConstI31Dispatch.i31_instruction_effect c irt iit start finish hcall
  intro t ht
  have hi32 : SpecTec.valtype.NumT .I32T ∈
      FiniteValidTypes.candidateUniverse c :=
    FiniteValidTypes.valid_mem_candidateUniverse c _ (by rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  cases ht
  exact hi32

theorem extern_convert_inputs_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.externop_) (iit : SpecTec.inferinstrtype)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«EXTERN.CONVERT» op)⟩)
      start (.success (.of iit)) finish) :
    ∀ t ∈ iit.1.INS.2,
      t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨hresult, _⟩ :=
    (ConstExternConvertDecision.extern_convert_success_iff_result
      c irt op iit start finish).1 hcall
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
      intro t hmem
      rw [hiit] at hmem
      have hvalid : ValtypeValidation.valtypeValid c
          (ConstExternConvertProduction.externInput nu op) = true := by
        cases nu <;> cases op <;> rfl
      have hcandidate := FiniteValidTypes.valid_mem_candidateUniverse c _ hvalid
      simp only [ConstExternConvertProduction.externInstrType,
        List.mem_cons, List.not_mem_nil, or_false] at hmem
      cases hmem
      exact hcandidate

end properties.wasm_module_ok.ConstBasicInputCandidate
