import properties.wasm_module_ok.ConstExternConvertDecision
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExternConvertProduction

def externInput (nu : SpecTec.null) (op : SpecTec.externop_) :
    SpecTec.valtype :=
  .RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1)

def externOutput (nu : SpecTec.null) (op : SpecTec.externop_) :
    SpecTec.valtype :=
  .RefT (.«% %» nu (ExternopTypeDecision.typeExternopResult op).2)

def externStep (irt : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) : Bool :=
  match PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 irt) with
  | none => false
  | some (.«% %» nu _) =>
    ([SpecTec.externop_.Internalize, .Externalize] : List SpecTec.externop_).any
      (fun op => decide (externInput nu op ∈ s) &&
        decide (u = externOutput nu op))

theorem extern_step_iff
    (irt : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) :
    externStep irt s u = true ↔
      ∃ (nu : SpecTec.null) (ht : SpecTec.heaptype)
        (op : SpecTec.externop_),
        PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 irt) =
          some (.«% %» nu ht) ∧
        externInput nu op ∈ s ∧
        u = externOutput nu op := by
  cases href : PeekRefDecision.peekRefResult
      (PeekDecision.peekResult 0 irt) with
  | none =>
    simp [externStep, href]
  | some rt =>
    cases rt with
    | «% %» nu ht =>
      simp only [externStep, href, List.any_eq_true,
        Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro ⟨op, _, hinput, houtput⟩
        exact ⟨nu, ht, op, rfl, hinput, houtput⟩
      · rintro ⟨nu', ht', op, hsame, hinput, houtput⟩
        cases Option.some.inj hsame
        exact ⟨op, by cases op <;> simp, hinput, houtput⟩

theorem extern_step_mono
    (irt : SpecTec.inferresulttype)
    (s t : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (hsub : s ⊆ t) (hstep : externStep irt s u = true) :
    externStep irt t u = true := by
  obtain ⟨nu, ht, op, href, hinput, hu⟩ :=
    (extern_step_iff irt s u).1 hstep
  exact (extern_step_iff irt t u).2
    ⟨nu, ht, op, href, hsub hinput, hu⟩

theorem extern_output_mem_candidate
    (c : SpecTec.context) (nu : SpecTec.null)
    (op : SpecTec.externop_) :
    externOutput nu op ∈ FiniteValidTypes.candidateUniverse c := by
  apply FiniteValidTypes.valid_mem_candidateUniverse
  cases nu <;> cases op <;>
    rfl

theorem extern_step_output_mem_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (hstep : externStep irt s u = true) :
    u ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨nu, _, op, _, _, rfl⟩ :=
    (extern_step_iff irt s u).1 hstep
  exact extern_output_mem_candidate c nu op

def externInstrType (nu : SpecTec.null) (op : SpecTec.externop_) :
    SpecTec.inferinstrtype :=
  ⟨{ INS := (.NoEllipses, [externInput nu op]),
     OUTS := (.NoEllipses, [externOutput nu op]) },
    ([] : List SpecTec.localidx)⟩

theorem extern_convert_result_of_peek
    (irt : SpecTec.inferresulttype) (nu : SpecTec.null)
    (ht : SpecTec.heaptype) (op : SpecTec.externop_)
    (hpeek : PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 irt) =
      some (.«% %» nu ht)) :
    ConstExternConvertDecision.externConvertResult irt op =
      some (externInstrType nu op) := by
  simp [ConstExternConvertDecision.externConvertResult, hpeek,
    externInstrType, externInput, externOutput]

theorem extern_step_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (start : Nat) :
    externStep irt s u = true ↔
      ∃ (nu : SpecTec.null) (ht : SpecTec.heaptype)
        (op : SpecTec.externop_),
        PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 irt) =
          some (.«% %» nu ht) ∧
        externInput nu op ∈ s ∧
        u = externOutput nu op ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.«EXTERN.CONVERT» op)⟩)
          start (.success (.of (externInstrType nu op))) start := by
  constructor
  · intro hstep
    obtain ⟨nu, ht, op, hpeek, hinput, hu⟩ :=
      (extern_step_iff irt s u).1 hstep
    refine ⟨nu, ht, op, hpeek, hinput, hu, ?_⟩
    exact (ConstExternConvertDecision.extern_convert_success_iff_result
      c irt op (externInstrType nu op) start start).2
      ⟨extern_convert_result_of_peek irt nu ht op hpeek, rfl⟩
  · rintro ⟨nu, ht, op, hpeek, hinput, hu, _⟩
    exact (extern_step_iff irt s u).2
      ⟨nu, ht, op, hpeek, hinput, hu⟩

theorem extern_convert_peek_of_result
    (irt : SpecTec.inferresulttype) (nu : SpecTec.null)
    (op : SpecTec.externop_)
    (hresult : ConstExternConvertDecision.externConvertResult irt op =
      some (externInstrType nu op)) :
    ∃ ht : SpecTec.heaptype,
      PeekRefDecision.peekRefResult (PeekDecision.peekResult 0 irt) =
        some (.«% %» nu ht) := by
  cases href : PeekRefDecision.peekRefResult
      (PeekDecision.peekResult 0 irt) with
  | none =>
    simp [ConstExternConvertDecision.externConvertResult, href] at hresult
  | some rt =>
    cases rt with
    | «% %» nu' ht =>
      have hnu : nu' = nu := by
        cases nu' <;> cases nu <;> cases op <;>
          simp_all [ConstExternConvertDecision.externConvertResult,
            externInstrType, externInput, externOutput,
            ExternopTypeDecision.typeExternopResult]
      subst nu'
      exact ⟨ht, rfl⟩

theorem extern_step_iff_instr_effect_exact
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (start : Nat) :
    externStep irt s u = true ↔
      ∃ (nu : SpecTec.null) (op : SpecTec.externop_),
        externInput nu op ∈ s ∧
        u = externOutput nu op ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.«EXTERN.CONVERT» op)⟩)
          start (.success (.of (externInstrType nu op))) start := by
  constructor
  · intro hstep
    obtain ⟨nu, _, op, _, hinput, hu, heval⟩ :=
      (extern_step_iff_instr_effect c irt s u start).1 hstep
    exact ⟨nu, op, hinput, hu, heval⟩
  · rintro ⟨nu, op, hinput, hu, heval⟩
    obtain ⟨hresult, _⟩ :=
      (ConstExternConvertDecision.extern_convert_success_iff_result
        c irt op (externInstrType nu op) start start).1 heval
    obtain ⟨ht, hpeek⟩ := extern_convert_peek_of_result irt nu op hresult
    exact (extern_step_iff irt s u).2
      ⟨nu, ht, op, hpeek, hinput, hu⟩

def externTypeStep (s : Finset SpecTec.valtype)
    (u : SpecTec.valtype) : Bool :=
  ([SpecTec.null.NoNull, .Null] : List SpecTec.null).any
    (fun nu =>
      ([SpecTec.externop_.Internalize, .Externalize] :
        List SpecTec.externop_).any
        (fun op => decide (externInput nu op ∈ s) &&
          decide (u = externOutput nu op)))

theorem extern_type_step_iff
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) :
    externTypeStep s u = true ↔
      ∃ (nu : SpecTec.null) (op : SpecTec.externop_),
        externInput nu op ∈ s ∧ u = externOutput nu op := by
  simp only [externTypeStep, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨nu, _, op, _, hinput, hu⟩
    exact ⟨nu, op, hinput, hu⟩
  · rintro ⟨nu, op, hinput, hu⟩
    exact ⟨nu, by cases nu <;> simp, op, by cases op <;> simp,
      hinput, hu⟩

theorem extern_type_step_mono
    (s t : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (hsub : s ⊆ t) (hstep : externTypeStep s u = true) :
    externTypeStep t u = true := by
  obtain ⟨nu, op, hinput, hu⟩ := (extern_type_step_iff s u).1 hstep
  exact (extern_type_step_iff t u).2
    ⟨nu, op, hsub hinput, hu⟩

theorem extern_type_step_output_mem_candidate
    (c : SpecTec.context) (s : Finset SpecTec.valtype)
    (u : SpecTec.valtype) (hstep : externTypeStep s u = true) :
    u ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨nu, op, _, rfl⟩ := (extern_type_step_iff s u).1 hstep
  exact extern_output_mem_candidate c nu op

theorem extern_type_step_iff_indexed
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) :
    externTypeStep s u = true ↔
      ∃ irt : SpecTec.inferresulttype, externStep irt s u = true := by
  constructor
  · intro hstep
    obtain ⟨nu, op, hinput, hu⟩ :=
      (extern_type_step_iff s u).1 hstep
    let irt : SpecTec.inferresulttype :=
      (.NoEllipses, [externInput nu op])
    have hpeek : PeekRefDecision.peekRefResult
        (PeekDecision.peekResult 0 irt) =
        some (.«% %» nu (ExternopTypeDecision.typeExternopResult op).1) := by
      rfl
    exact ⟨irt, (extern_step_iff irt s u).2
      ⟨nu, (ExternopTypeDecision.typeExternopResult op).1,
        op, hpeek, hinput, hu⟩⟩
  · rintro ⟨irt, hstep⟩
    obtain ⟨nu, _, op, _, hinput, hu⟩ :=
      (extern_step_iff irt s u).1 hstep
    exact (extern_type_step_iff s u).2 ⟨nu, op, hinput, hu⟩

theorem extern_type_step_iff_instruction
    (c : SpecTec.context) (s : Finset SpecTec.valtype)
    (u : SpecTec.valtype) (start : Nat) :
    externTypeStep s u = true ↔
      ∃ (irt : SpecTec.inferresulttype) (nu : SpecTec.null)
        (op : SpecTec.externop_),
        ConstSyntaxDecision.syntaxAllowed c (.«EXTERN.CONVERT» op) = true ∧
        externInput nu op ∈ s ∧
        u = externOutput nu op ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c irt (.«EXTERN.CONVERT» op)⟩)
          start (.success (.of (externInstrType nu op))) start := by
  constructor
  · intro hstep
    obtain ⟨irt, hindexed⟩ :=
      (extern_type_step_iff_indexed s u).1 hstep
    obtain ⟨nu, op, hinput, hu, heval⟩ :=
      (extern_step_iff_instr_effect_exact c irt s u start).1 hindexed
    refine ⟨irt, nu, op, ?_, hinput, hu, heval⟩
    simp [ConstSyntaxDecision.syntaxAllowed,
      ConstArithmeticValidation.arithmeticOps]
  · rintro ⟨irt, nu, op, _, hinput, hu, heval⟩
    apply (extern_type_step_iff_indexed s u).2
    exact ⟨irt,
      (extern_step_iff_instr_effect_exact c irt s u start).2
        ⟨nu, op, hinput, hu, heval⟩⟩

def externTypeOutputs (c : SpecTec.context)
    (s : Finset SpecTec.valtype) : Finset SpecTec.valtype :=
  (FiniteValidTypes.candidateUniverse c).filter
    (fun u => externTypeStep s u = true)

theorem extern_type_outputs_mem_iff
    (c : SpecTec.context) (s : Finset SpecTec.valtype)
    (u : SpecTec.valtype) :
    u ∈ externTypeOutputs c s ↔ externTypeStep s u = true := by
  simp only [externTypeOutputs, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hstep
    exact ⟨extern_type_step_output_mem_candidate c s u hstep, hstep⟩

theorem extern_type_outputs_mono
    (c : SpecTec.context) (s t : Finset SpecTec.valtype)
    (hsub : s ⊆ t) :
    externTypeOutputs c s ⊆ externTypeOutputs c t := by
  intro u hu
  exact (extern_type_outputs_mem_iff c t u).2
    (extern_type_step_mono s t u hsub
      ((extern_type_outputs_mem_iff c s u).1 hu))

end properties.wasm_module_ok.ConstExternConvertProduction
