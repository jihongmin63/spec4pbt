import properties.wasm_module_ok.InstrsLocalClosure
import properties.wasm_module_ok.CandidateUniverseStatic

set_option autoImplicit false

namespace properties.wasm_module_ok.InstrsCandidateClosure

theorem instrs_candidate_entries_closed
    (base : SpecTec.context) (xs : List SpecTec.instr) :
    (∀ i ∈ xs,
      ∀ (c : SpecTec.context) (irt : SpecTec.inferresulttype)
        (iit : SpecTec.inferinstrtype) (n fin : Nat),
      FiniteValidTypes.candidateUniverse c =
        FiniteValidTypes.candidateUniverse base →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.Call.Instr_ok c irt i⟩)
        n (.success (.of iit)) fin →
      ∃ need outs : List SpecTec.valtype,
        iit.1.INS = (.NoEllipses, need) ∧
        iit.1.OUTS = (.NoEllipses, outs) ∧
        ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse base) →
    ∀ (c : SpecTec.context) (stack : List SpecTec.valtype)
      (result : SpecTec.inferresulttype × List SpecTec.idx)
      (start fin : Nat),
    FiniteValidTypes.candidateUniverse c =
      FiniteValidTypes.candidateUniverse base →
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c (.NoEllipses, stack) xs⟩)
      start (.success (.of result)) fin →
    (∀ t ∈ stack, t ∈ FiniteValidTypes.candidateUniverse base) →
    result.1.1 = .NoEllipses ∧
      ∀ t ∈ result.1.2,
        t ∈ FiniteValidTypes.candidateUniverse base := by
  induction xs with
  | nil =>
    intro _ c stack result start fin _ h hstack
    obtain ⟨hr, _⟩ :=
      (InstrsValidation.instrs_nil_success_iff
        c (.NoEllipses, stack) result start fin).1 h
    subst result
    exact ⟨rfl, hstack⟩
  | cons i rest ih =>
    intro hstep c stack result start fin hc h hstack
    obtain ⟨iit, c₁, popped, pushed,
      middle₁, middle₂, middle₃, middle₄,
      hinstr, hinit, hpop, hpush, hrest⟩ :=
      (InstrsValidation.instrs_cons_success_iff
        c (.NoEllipses, stack) i rest result start fin).1 h
    obtain ⟨need, outs, hins, houts, hclosed⟩ :=
      hstep i (by simp) c (.NoEllipses, stack) iit
        start middle₁ hc hinstr
    have hpop' : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.Call.«$pop» c
            (.NoEllipses, need) (.NoEllipses, stack)⟩)
        middle₂ (.success (.of popped)) middle₃ := by
      simpa [hins] using hpop
    have hpush' : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.Call.«$push» c
            (.NoEllipses, outs) popped⟩)
        middle₃ (.success (.of pushed)) middle₄ := by
      simpa [houts] using hpush
    have hpopped := PopResult.pop_noellipses_success_result
      c need stack popped middle₂ middle₃ hpop'
    have hclosedP :
        ∀ t ∈ pushed.2,
          t ∈ FiniteValidTypes.candidateUniverse base :=
      StackClosure.pop_push_entries_closed
        c need outs stack popped pushed middle₂ middle₃ middle₄
        hpop' hpush' (fun t => t ∈ FiniteValidTypes.candidateUniverse base)
        hstack hclosed
    subst popped
    have hpushResult := (PushValidation.push_success_iff_result
      c (.NoEllipses, outs)
        (.NoEllipses, stack.take (stack.length - need.length))
        pushed middle₃ middle₄).1 hpush'
    have hs :
        pushed = (.NoEllipses,
          stack.take (stack.length - need.length) ++ outs) := by
      simpa [PushValidation.pushResult] using hpushResult.1.symm
    rw [hs] at hrest hclosedP
    have hc₁ : FiniteValidTypes.candidateUniverse c₁ =
        FiniteValidTypes.candidateUniverse base :=
      (CandidateUniverseStatic.candidateUniverse_of_init_locals
        c c₁ iit.2 middle₁ middle₂ hinit).trans hc
    have hrestStep :
        ∀ j ∈ rest,
          ∀ (c : SpecTec.context) (irt : SpecTec.inferresulttype)
            (iit : SpecTec.inferinstrtype) (n fin : Nat),
          FiniteValidTypes.candidateUniverse c =
            FiniteValidTypes.candidateUniverse base →
          SpecTecExecution.Eval SpecTec.Body
            (.call ⟨SpecTec.inferinstrtype,
              SpecTec.Call.Instr_ok c irt j⟩)
            n (.success (.of iit)) fin →
          ∃ need outs : List SpecTec.valtype,
            iit.1.INS = (.NoEllipses, need) ∧
            iit.1.OUTS = (.NoEllipses, outs) ∧
            ∀ t ∈ outs,
              t ∈ FiniteValidTypes.candidateUniverse base := by
      intro j hj
      exact hstep j (by simp [hj])
    exact ih hrestStep c₁
      (stack.take (stack.length - need.length) ++ outs)
      result middle₄ fin hc₁ hrest hclosedP

end properties.wasm_module_ok.InstrsCandidateClosure
