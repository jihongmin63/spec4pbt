import properties.wasm_module_ok.ConstInstrsMatchClosure
import properties.wasm_module_ok.ConstProductiveStaticStackStep
import properties.wasm_module_ok.ConstInputShape
import properties.wasm_module_ok.InstrsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstInstrsProductiveClosure

/-- A successful sequence of constant instructions never leaves the finite
productive closure. The bound is on the number of instructions, not stack
height. -/
theorem instrs_entries_in_productive_closure
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (origin : SpecTec.context)
    (horigin : origin ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (xs : List SpecTec.instr) :
    (∀ i ∈ xs, ConstSyntaxDecision.syntaxAllowed origin i = true) →
    ∀ (current : SpecTec.context)
      (stack : List SpecTec.valtype)
      (result : SpecTec.inferresulttype × List SpecTec.idx)
      (round start finish : Nat),
      ConstStaticAgreement.StaticAgreement origin current →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.Call.Instrs_ok current
            (.NoEllipses, stack) xs⟩)
        start (.success (.of result)) finish →
      (∀ t ∈ stack,
        t ∈ FiniteClosure.iterate
          (ConstProductiveClosure.productiveStep origin) round) →
      (∀ t ∈ stack, CandidateValMatch.InTableVal origin t) →
      result.1.1 = .NoEllipses ∧
      (∀ t ∈ result.1.2,
        t ∈ FiniteClosure.iterate
          (ConstProductiveClosure.productiveStep origin)
          (round + xs.length)) ∧
      (∀ t ∈ result.1.2,
        CandidateValMatch.InTableVal origin t) := by
  induction xs with
  | nil =>
    intro _ current stack result round start finish _ hcall hstack htable
    obtain ⟨hr, _⟩ :=
      (InstrsValidation.instrs_nil_success_iff
        current (.NoEllipses, stack) result start finish).1 hcall
    subst result
    exact ⟨rfl, by simpa using hstack, htable⟩
  | cons i rest ih =>
    intro hall current stack result round start finish
      hstatic hcall hstack htable
    have hi : ConstSyntaxDecision.syntaxAllowed origin i = true :=
      hall i (by simp)
    have hrestSyntax : ∀ j ∈ rest,
        ConstSyntaxDecision.syntaxAllowed origin j = true := by
      intro j hj
      exact hall j (by simp [hj])
    obtain ⟨iit, next, popped, pushed,
      middle₁, middle₂, middle₃, middle₄,
      hinstr, hinit, hpop, hpush, hrest⟩ :=
      (InstrsValidation.instrs_cons_success_iff
        current (.NoEllipses, stack) i rest result
        start finish).1 hcall
    have hsyntaxCurrent :
        ConstSyntaxDecision.syntaxAllowed current i = true := by
      rw [← ConstStaticAgreement.syntax_allowed origin current hstatic i]
      exact hi
    have hsyntax :=
      (ConstSyntaxDecision.syntaxAllowed_iff current i).1 hsyntaxCurrent
    have hconst : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$is_const» current i⟩)
        start (.success (.of true)) start :=
      ConstAdditionalSyntaxValidation.syntax_is_const
        current i start hsyntax
    have hins :=
      ConstInputShape.is_const_instruction_noellipses_inputs
        current (.NoEllipses, stack) i iit
        start start middle₁ hconst hinstr
    have hpop' : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.Call.«$pop» current
            (.NoEllipses, iit.1.INS.2) (.NoEllipses, stack)⟩)
        middle₂ (.success (.of popped)) middle₃ := by
      rw [hins] at hpop
      exact hpop
    have hclosed := ConstProductiveStaticStackStep.static_stack_entries_next_round
      m tr origin current horigin hstatic
      (.NoEllipses, stack) i iit stack popped pushed round
      start start middle₁ middle₂ middle₃ middle₄
      hconst hinstr hpop' hpush hstack htable
    obtain ⟨u, houts⟩ :=
      ConstSyntaxSingleton.is_const_instruction_singleton_outputs
        current (.NoEllipses, stack) i iit
        start start middle₁ hconst hinstr
    have hpopped := PopResult.pop_noellipses_success_result
      current iit.1.INS.2 stack popped middle₂ middle₃ hpop'
    have hpushResult :=
      ((PushValidation.push_success_iff_result
        current iit.1.OUTS popped pushed middle₃ middle₄).1 hpush).1
    have hpushed : pushed =
        (.NoEllipses,
          stack.take (stack.length - iit.1.INS.2.length) ++ [u]) := by
      simp only [houts, hpopped, PushValidation.pushResult,
        Option.some.injEq] at hpushResult
      exact hpushResult.symm
    have hstaticNext := ConstStaticAgreement.after_init_locals
      origin current next iit.2 middle₁ middle₂ hstatic hinit
    have hnextStack : ∀ t ∈
        stack.take (stack.length - iit.1.INS.2.length) ++ [u],
        t ∈ FiniteClosure.iterate
          (ConstProductiveClosure.productiveStep origin) (round + 1) := by
      intro t ht
      exact hclosed.1 t (by simpa [hpushed] using ht)
    have hnextTable : ∀ t ∈
        stack.take (stack.length - iit.1.INS.2.length) ++ [u],
        CandidateValMatch.InTableVal origin t := by
      intro t ht
      exact hclosed.2 t (by simpa [hpushed] using ht)
    have hrest' : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.Call.Instrs_ok next
            (.NoEllipses,
              stack.take (stack.length - iit.1.INS.2.length) ++ [u])
            rest⟩)
        middle₄ (.success (.of result)) finish := by
      simpa only [hpushed] using hrest
    have hresult := ih hrestSyntax next
      (stack.take (stack.length - iit.1.INS.2.length) ++ [u])
      result (round + 1) middle₄ finish
      hstaticNext hrest' hnextStack hnextTable
    have hindex : (round + 1) + rest.length =
        round + (i :: rest).length := by
      simp only [List.length_cons]
      omega
    exact ⟨hresult.1, by simpa only [hindex] using hresult.2.1,
      hresult.2.2⟩

end properties.wasm_module_ok.ConstInstrsProductiveClosure
