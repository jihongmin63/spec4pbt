import properties.wasm_module_ok.ConstDecisionTrace
import properties.wasm_module_ok.InstrsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStepTrace

theorem const_ok_cons_success_iff
    (c : SpecTec.context) (t : SpecTec.valtype)
    (i : SpecTec.instr) (rest : List SpecTec.instr)
    (n fin : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t (i :: rest)⟩)
      n (.success (.of ())) fin ↔
    ConstSyntaxDecision.syntaxAllowed c i = true ∧
    (∀ j ∈ rest, ConstSyntaxDecision.syntaxAllowed c j = true) ∧
    ∃ (iit : SpecTec.inferinstrtype) (c₁ : SpecTec.context)
      (popped pushed irt : SpecTec.inferresulttype)
      (indices : List SpecTec.idx) (ellipses : SpecTec.ellipses)
      (middle₁ middle₂ middle₃ middle₄ finInstrs : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c (.NoEllipses, []) i⟩)
        n (.success (.of iit)) middle₁ ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.«$init_locals» c iit.2⟩)
        middle₁ (.success (.of c₁)) middle₂ ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.SpecTecCall.«$pop» c iit.1.INS (.NoEllipses, [])⟩)
        middle₂ (.success (.of popped)) middle₃ ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.SpecTecCall.«$push» c iit.1.OUTS popped⟩)
        middle₃ (.success (.of pushed)) middle₄ ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.SpecTecCall.Instrs_ok c₁ pushed rest⟩)
        middle₄ (.success (.of (irt, indices))) finInstrs ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.ellipses × SpecTec.resulttype,
          SpecTec.SpecTecCall.«$pop» c
            (.NoEllipses, [t]) irt⟩)
        finInstrs
          (.success (.of (ellipses, ([] : List SpecTec.valtype))))
          fin := by
  rw [ConstDecisionTrace.const_ok_decision_trace_iff]
  constructor
  · rintro ⟨hall, irt, indices, ellipses, middle, hlist, hfinal⟩
    obtain ⟨iit, c₁, popped, pushed,
      middle₁, middle₂, middle₃, middle₄,
      hinstr, hinit, hpop, hpush, hrest⟩ :=
      (InstrsValidation.instrs_cons_success_iff
        c (.NoEllipses, []) i rest (irt, indices) n middle).1 hlist
    exact ⟨hall i (by simp),
      (fun j hj => hall j (by simp [hj])),
      iit, c₁, popped, pushed, irt, indices, ellipses,
      middle₁, middle₂, middle₃, middle₄, middle,
      hinstr, hinit, hpop, hpush, hrest, hfinal⟩
  · rintro ⟨hi, hrestSyntax, iit, c₁, popped, pushed,
      irt, indices, ellipses, middle₁, middle₂, middle₃,
      middle₄, finInstrs,
      hinstr, hinit, hpop, hpush, hrest, hfinal⟩
    have hlist :=
      (InstrsValidation.instrs_cons_success_iff
        c (.NoEllipses, []) i rest (irt, indices) n finInstrs).2
        ⟨iit, c₁, popped, pushed, middle₁, middle₂, middle₃,
          middle₄, hinstr, hinit, hpop, hpush, hrest⟩
    exact ⟨(fun j hj => by
      rcases List.mem_cons.mp hj with rfl | htail
      · exact hi
      · exact hrestSyntax j htail),
      irt, indices, ellipses, finInstrs, hlist, hfinal⟩

end properties.wasm_module_ok.ConstStepTrace
