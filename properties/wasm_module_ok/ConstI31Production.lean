import properties.wasm_module_ok.ConstI31Dispatch
import properties.wasm_module_ok.ConstSyntaxDecision
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstI31Production

/-- `REF.I31` consumes one fillable `i32` and produces one `i31ref`. -/
def i31Step (s : Finset SpecTec.valtype)
    (u : SpecTec.valtype) : Bool :=
  decide (SpecTec.valtype.NumT .I32T ∈ s) &&
    decide (u = .RefT (.«% %» .NoNull .I31HT))

theorem i31_step_iff (s : Finset SpecTec.valtype)
    (u : SpecTec.valtype) :
    i31Step s u = true ↔
      SpecTec.valtype.NumT .I32T ∈ s ∧
      u = .RefT (.«% %» .NoNull .I31HT) := by
  simp [i31Step]

def i31Outputs (c : SpecTec.context)
    (s : Finset SpecTec.valtype) : Finset SpecTec.valtype :=
  (FiniteValidTypes.candidateUniverse c).filter
    (fun u => i31Step s u = true)

theorem i31_outputs_mem_iff (c : SpecTec.context)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) :
    u ∈ i31Outputs c s ↔ i31Step s u = true := by
  simp only [i31Outputs, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hstep
    obtain ⟨_, rfl⟩ := (i31_step_iff s u).1 hstep
    have hvalid : ValtypeValidation.valtypeValid c
        (.RefT (.«% %» .NoNull .I31HT)) = true := by rfl
    exact ⟨FiniteValidTypes.valid_mem_candidateUniverse c _ hvalid, hstep⟩

theorem i31_step_mono
    (s t : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (hsub : s ⊆ t) (h : i31Step s u = true) :
    i31Step t u = true := by
  obtain ⟨hmem, hout⟩ := (i31_step_iff s u).1 h
  exact (i31_step_iff t u).2 ⟨hsub hmem, hout⟩

theorem i31_step_iff_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) (n : Nat) :
    i31Step s u = true ↔
      SpecTec.valtype.NumT .I32T ∈ s ∧
      u = .RefT (.«% %» .NoNull .I31HT) ∧
      ConstSyntaxDecision.syntaxAllowed c .«REF.I31» = true ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.Call.Instr_ok c irt .«REF.I31»⟩)
        n (.success (.of
          (⟨{ INS := (.NoEllipses, [.NumT .I32T]),
               OUTS := (.NoEllipses, [u]) },
            ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype))) n := by
  constructor
  · intro hstep
    obtain ⟨hmem, hout⟩ := (i31_step_iff s u).1 hstep
    subst u
    refine ⟨hmem, rfl, ?_, ?_⟩
    · exact (ConstSyntaxDecision.syntaxAllowed_iff c .«REF.I31»).2
        .refI31
    · exact ConstI31Dispatch.i31_dispatch_total c irt n
  · rintro ⟨hmem, rfl, _, _⟩
    exact (i31_step_iff s _).2 ⟨hmem, rfl⟩

theorem i31_step_of_instr_effect
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype)
    (iit : SpecTec.inferinstrtype) (start fin : Nat)
    (hinput : SpecTec.valtype.NumT .I32T ∈ s)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt .«REF.I31»⟩)
      start (.success (.of iit)) fin)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    i31Step s u = true := by
  obtain ⟨heffect, _⟩ :=
    ConstI31Dispatch.i31_instruction_effect c irt iit start fin hcall
  have hu : u = .RefT (.«% %» .NoNull .I31HT) := by
    rw [heffect] at houts
    simpa using houts.symm
  exact (i31_step_iff s u).2 ⟨hinput, hu⟩

end properties.wasm_module_ok.ConstI31Production
