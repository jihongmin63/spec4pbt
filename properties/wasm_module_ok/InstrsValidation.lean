import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.InstrsValidation

theorem instrs_nil_total (c : SpecTec.context)
    (irt : SpecTec.inferresulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.SpecTecCall.Instrs_ok c irt []⟩)
      n (.success (.of (irt, ([] : List SpecTec.idx)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Instrs_ok_clauses c irt []) ())
    n (.success (.of (irt, ([] : List SpecTec.idx)))) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Instrs_ok:clause:0» c irt [])
    n (.success (.of (irt, ([] : List SpecTec.idx)))) n
  unfold SpecTec.«Instrs_ok:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · apply SpecTecExecution.Eval.guard_true
    rfl
  · exact SpecTecExecution.Eval.pure (irt, ([] : List SpecTec.idx))

theorem instrs_nil_success_iff (c : SpecTec.context)
    (irt : SpecTec.inferresulttype)
    (result : SpecTec.inferresulttype × List SpecTec.idx)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.SpecTecCall.Instrs_ok c irt []⟩)
      n (.success (.of result)) finalSupply ↔
    result = (irt, ([] : List SpecTec.idx)) ∧ finalSupply = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h (instrs_nil_total c irt n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact instrs_nil_total c irt finalSupply

theorem instrs_cons_success_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (instr : SpecTec.instr) (rest : List SpecTec.instr)
    (result : SpecTec.inferresulttype × List SpecTec.idx)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.SpecTecCall.Instrs_ok c irt (instr :: rest)⟩)
      n (.success (.of result)) finalSupply ↔
    ∃ (iit : SpecTec.inferinstrtype) (c₁ : SpecTec.context)
      (popped pushed : SpecTec.inferresulttype)
      (middle₁ middle₂ middle₃ middle₄ : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.SpecTecCall.Instr_ok c irt instr⟩)
        n (.success (.of iit)) middle₁ ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.«$init_locals» c iit.2⟩)
        middle₁ (.success (.of c₁)) middle₂ ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.SpecTecCall.«$pop» c iit.1.INS irt⟩)
        middle₂ (.success (.of popped)) middle₃ ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.SpecTecCall.«$push» c iit.1.OUTS popped⟩)
        middle₃ (.success (.of pushed)) middle₄ ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.SpecTecCall.Instrs_ok c₁ pushed rest⟩)
        middle₄ (.success (.of result)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Instrs_ok:clause:0» c irt (instr :: rest))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«Instrs_ok:clause:1» c irt
              (instr :: rest)] ()))
        n (.success (.of result)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Instrs_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond => simp at hcond
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Instrs_ok:clause:1» c irt
              (instr :: rest))
            (fun _ => .unmatch))
          n (.success (.of result)) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Instrs_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard htail =>
            cases hguard with
            | guard_true _ =>
              cases htail with
              | bind_success hinstr htail =>
                rename_i middle₁ iit
                cases htail with
                | bind_success hinit htail =>
                  rename_i middle₂ c₁
                  cases htail with
                  | bind_success hpop htail =>
                    rename_i middle₃ popped
                    cases htail with
                    | bind_success hpush htail =>
                      rename_i middle₄ pushed
                      cases htail with
                      | bind_success hrest hpure =>
                        cases hpure with
                        | pure => exact ⟨iit, c₁, popped, pushed,
                            middle₁, middle₂, middle₃, middle₄,
                            hinstr, hinit, hpop, hpush, hrest⟩
        | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨iit, c₁, popped, pushed,
      middle₁, middle₂, middle₃, middle₄,
      hinstr, hinit, hpop, hpush, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Instrs_ok_clauses c irt (instr :: rest)) ())
      n (.success (.of result)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Instrs_ok:clause:0» c irt (instr :: rest))
        n .unmatch n
      unfold SpecTec.«Instrs_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Instrs_ok:clause:1» c irt (instr :: rest))
        n (.success (.of result)) finalSupply
      unfold SpecTec.«Instrs_ok:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · apply SpecTecExecution.Eval.guard_true
        rfl
      · apply SpecTecExecution.Eval.bind_success hinstr
        apply SpecTecExecution.Eval.bind_success hinit
        apply SpecTecExecution.Eval.bind_success hpop
        apply SpecTecExecution.Eval.bind_success hpush
        apply SpecTecExecution.Eval.bind_success hrest
        exact SpecTecExecution.Eval.pure result

end properties.wasm_module_ok.InstrsValidation
