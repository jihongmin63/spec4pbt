import properties.wasm_module_ok.InstrsClosure

set_option autoImplicit false

namespace properties.wasm_module_ok.InstrsLocalClosure

theorem instrs_preserves_entries_of_members
    (P : SpecTec.valtype → Prop)
    (xs : List SpecTec.instr) :
    (∀ i ∈ xs,
      ∀ (c : SpecTec.context) (irt : SpecTec.inferresulttype)
        (iit : SpecTec.inferinstrtype) (n fin : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.Call.Instr_ok c irt i⟩)
        n (.success (.of iit)) fin →
      ∃ need outs : List SpecTec.valtype,
        iit.1.INS = (.NoEllipses, need) ∧
        iit.1.OUTS = (.NoEllipses, outs) ∧
        ∀ t ∈ outs, P t) →
    ∀ (c : SpecTec.context) (stack : List SpecTec.valtype)
      (result : SpecTec.inferresulttype × List SpecTec.idx)
      (start fin : Nat),
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c (.NoEllipses, stack) xs⟩)
      start (.success (.of result)) fin →
    (∀ t ∈ stack, P t) →
    result.1.1 = .NoEllipses ∧ ∀ t ∈ result.1.2, P t := by
  induction xs with
  | nil =>
    intro _ c stack result start fin h hstack
    obtain ⟨hr, _⟩ :=
      (InstrsValidation.instrs_nil_success_iff
        c (.NoEllipses, stack) result start fin).1 h
    subst result
    exact ⟨rfl, hstack⟩
  | cons i rest ih =>
    intro hstep c stack result start fin h hstack
    obtain ⟨iit, c₁, popped, pushed,
      middle₁, middle₂, middle₃, middle₄,
      hinstr, _, hpop, hpush, hrest⟩ :=
      (InstrsValidation.instrs_cons_success_iff
        c (.NoEllipses, stack) i rest result start fin).1 h
    obtain ⟨need, outs, hins, houts, hclosed⟩ :=
      hstep i (by simp) c (.NoEllipses, stack) iit start middle₁ hinstr
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
    have hclosedP : ∀ t ∈ pushed.2, P t :=
      StackClosure.pop_push_entries_closed
        c need outs stack popped pushed middle₂ middle₃ middle₄
        hpop' hpush' P hstack hclosed
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
    have hrestStep :
        ∀ j ∈ rest,
          ∀ (c : SpecTec.context) (irt : SpecTec.inferresulttype)
            (iit : SpecTec.inferinstrtype) (n fin : Nat),
          SpecTecExecution.Eval SpecTec.Body
            (.call ⟨SpecTec.inferinstrtype,
              SpecTec.Call.Instr_ok c irt j⟩)
            n (.success (.of iit)) fin →
          ∃ need outs : List SpecTec.valtype,
            iit.1.INS = (.NoEllipses, need) ∧
            iit.1.OUTS = (.NoEllipses, outs) ∧
            ∀ t ∈ outs, P t := by
      intro j hj
      exact hstep j (by simp [hj])
    exact ih hrestStep c₁
      (stack.take (stack.length - need.length) ++ outs)
      result middle₄ fin hrest hclosedP

end properties.wasm_module_ok.InstrsLocalClosure
