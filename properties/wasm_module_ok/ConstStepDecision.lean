import properties.wasm_module_ok.ConstInstrDecision
import properties.wasm_module_ok.PopNoEllipsesDecision
import properties.wasm_module_ok.PushValidation
import properties.wasm_module_ok.LocalInitValidation
import properties.wasm_module_ok.ConstSyntaxSingleton

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstStepDecision

/-- Compute the stack after one constant-eligible instruction.  A successful
instruction has a concrete input stack, so the other shape is unreachable on
successful traces. -/
def constantStepResult (c : SpecTec.context)
    (available : List SpecTec.valtype) (i : SpecTec.instr) :
    Option SpecTec.inferresulttype := do
  let iit ← ConstInstrDecision.constantInstructionResult c
    (.NoEllipses, available) i
  match iit.1.INS with
  | (.NoEllipses, need) =>
      let popped ← PopNoEllipsesDecision.popResult c need available
      PushValidation.pushResult iit.1.OUTS popped
  | _ => none

theorem constant_step_result_iff_components
    (c : SpecTec.context) (available : List SpecTec.valtype)
    (i : SpecTec.instr) (pushed : SpecTec.inferresulttype) :
    constantStepResult c available i = some pushed ↔
      ∃ (iit : SpecTec.inferinstrtype)
        (need : List SpecTec.valtype)
        (popped : SpecTec.inferresulttype),
        ConstInstrDecision.constantInstructionResult c
          (.NoEllipses, available) i = some iit ∧
        iit.1.INS = (.NoEllipses, need) ∧
        PopNoEllipsesDecision.popResult c need available = some popped ∧
        PushValidation.pushResult iit.1.OUTS popped = some pushed := by
  constructor
  · intro h
    unfold constantStepResult at h
    cases hi : ConstInstrDecision.constantInstructionResult c
        (.NoEllipses, available) i with
    | none => simp [hi] at h
    | some iit =>
        cases hins : iit.1.INS with
        | mk dots need =>
          cases dots with
          | Ellipses => simp [hi, hins] at h
          | NoEllipses =>
              cases hp : PopNoEllipsesDecision.popResult c need available with
              | none => simp [hi, hins, hp] at h
              | some popped =>
                  exact ⟨iit, need, popped, rfl, hins, hp,
                    by simpa [hi, hins, hp] using h⟩
  · rintro ⟨iit, need, popped, hi, hins, hp, hpush⟩
    simp [constantStepResult, hi, hins, hp, hpush]

theorem constant_step_result_iff_calls
    (c : SpecTec.context) (available : List SpecTec.valtype)
    (i : SpecTec.instr) (pushed : SpecTec.inferresulttype) (n : Nat)
    (hready : CandidateTypeReady.Ready c)
    (havailable : ∀ t ∈ available,
      CandidateValMatch.InTableVal c t)
    (hinputs : ∀ iit need,
      ConstInstrDecision.constantInstructionResult c
        (.NoEllipses, available) i = some iit →
      iit.1.INS = (.NoEllipses, need) →
      ∀ t ∈ need, CandidateValMatch.InTableVal c t) :
    constantStepResult c available i = some pushed ↔
      ConstSyntaxDecision.syntaxAllowed c i = true ∧
      ∃ (iit : SpecTec.inferinstrtype)
        (popped : SpecTec.inferresulttype),
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferinstrtype,
            SpecTec.Call.Instr_ok c
              (.NoEllipses, available) i⟩)
          n (.success (.of iit)) n ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.context,
            SpecTec.Call.«$init_locals» c iit.2⟩)
          n (.success (.of c)) n ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferresulttype,
            SpecTec.Call.«$pop» c iit.1.INS
              (.NoEllipses, available)⟩)
          n (.success (.of popped)) n ∧
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨SpecTec.inferresulttype,
            SpecTec.Call.«$push» c iit.1.OUTS popped⟩)
          n (.success (.of pushed)) n := by
  constructor
  · intro hstep
    obtain ⟨iit, need, popped, hi, hins, hp, hpush⟩ :=
      (constant_step_result_iff_components c available i pushed).1 hstep
    obtain ⟨hallowed, hcall⟩ :=
      (ConstInstrDecision.constant_instruction_result_iff
        c (.NoEllipses, available) i iit n n).1 ⟨hi, rfl⟩
    have hlocals : iit.2 = [] :=
      (ConstInstrDecision.constant_instruction_input_shape
        c (.NoEllipses, available) i iit hi).choose_spec.2
    have hinit : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context,
          SpecTec.Call.«$init_locals» c iit.2⟩)
        n (.success (.of c)) n := by
      apply (LocalInitValidation.init_locals_success_iff_result
        c iit.2 c n n).2
      simp [hlocals, LocalInitValidation.initLocalsResult]
    have hpop : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.Call.«$pop» c iit.1.INS
            (.NoEllipses, available)⟩)
        n (.success (.of popped)) n := by
      rw [hins]
      exact (PopNoEllipsesDecision.pop_result_iff
        c need available popped n hready
        (hinputs iit need hi hins) havailable).1 hp
    have hpushCall :=
      (PushValidation.push_success_iff_result
        c iit.1.OUTS popped pushed n n).2 ⟨hpush, rfl⟩
    exact ⟨hallowed, iit, popped, hcall, hinit, hpop, hpushCall⟩
  · rintro ⟨hallowed, iit, popped, hcall, hinit, hpop, hpush⟩
    have hi :=
      (ConstInstrDecision.constant_instruction_result_iff
        c (.NoEllipses, available) i iit n n).2
        ⟨hallowed, hcall⟩ |>.1
    obtain ⟨need, hins, hlocal⟩ :=
      ConstInstrDecision.constant_instruction_input_shape
        c (.NoEllipses, available) i iit hi
    have hp : PopNoEllipsesDecision.popResult c need available =
        some popped := by
      rw [hins] at hpop
      exact (PopNoEllipsesDecision.pop_result_iff
        c need available popped n hready
        (hinputs iit need hi hins) havailable).2 hpop
    have hpushResult : PushValidation.pushResult iit.1.OUTS popped =
        some pushed :=
      ((PushValidation.push_success_iff_result
        c iit.1.OUTS popped pushed n n).1 hpush).1
    exact (constant_step_result_iff_components
      c available i pushed).2
      ⟨iit, need, popped, hi, hins, hp, hpushResult⟩

theorem constant_step_result_concrete_stack
    (c : SpecTec.context) (available : List SpecTec.valtype)
    (i : SpecTec.instr) (pushed : SpecTec.inferresulttype)
    (hstep : constantStepResult c available i = some pushed) :
    ∃ next : List SpecTec.valtype,
      pushed = (.NoEllipses, next) := by
  obtain ⟨iit, need, popped, hi, hins, hp, hpush⟩ :=
    (constant_step_result_iff_components c available i pushed).1 hstep
  obtain ⟨hallowed, hcall⟩ :=
    (ConstInstrDecision.constant_instruction_result_iff
      c (.NoEllipses, available) i iit 0 0).1 ⟨hi, rfl⟩
  obtain ⟨u, houts⟩ :=
    ConstSyntaxSingleton.syntax_instruction_singleton_outputs
      c (.NoEllipses, available) i iit 0 0
      ((ConstSyntaxDecision.syntaxAllowed_iff c i).1 hallowed) hcall
  have hpopshape : ∃ remaining : List SpecTec.valtype,
      popped = (.NoEllipses, remaining) := by
    unfold PopNoEllipsesDecision.popResult at hp
    split at hp
    · split at hp
      · cases hp
        exact ⟨_, rfl⟩
      · simp at hp
    · simp at hp
  obtain ⟨remaining, rfl⟩ := hpopshape
  rw [houts] at hpush
  simp [PushValidation.pushResult] at hpush
  subst pushed
  exact ⟨remaining ++ [u], rfl⟩

def StepCalls (c : SpecTec.context)
    (available : List SpecTec.valtype) (i : SpecTec.instr)
    (pushed : SpecTec.inferresulttype)
    (start middle₁ middle₂ middle₃ finish : Nat) : Prop :=
  ConstSyntaxDecision.syntaxAllowed c i = true ∧
    ∃ (iit : SpecTec.inferinstrtype)
      (popped : SpecTec.inferresulttype),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferinstrtype,
          SpecTec.Call.Instr_ok c
            (.NoEllipses, available) i⟩)
        start (.success (.of iit)) middle₁ ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context,
          SpecTec.Call.«$init_locals» c iit.2⟩)
        middle₁ (.success (.of c)) middle₂ ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.Call.«$pop» c iit.1.INS
            (.NoEllipses, available)⟩)
        middle₂ (.success (.of popped)) middle₃ ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.Call.«$push» c iit.1.OUTS popped⟩)
        middle₃ (.success (.of pushed)) finish

theorem constant_step_calls_any_counters
    (c : SpecTec.context) (available : List SpecTec.valtype)
    (i : SpecTec.instr) (pushed : SpecTec.inferresulttype)
    (start middle₁ middle₂ middle₃ finish : Nat)
    (hready : CandidateTypeReady.Ready c)
    (havailable : ∀ t ∈ available,
      CandidateValMatch.InTableVal c t)
    (hinputs : ∀ iit need,
      ConstInstrDecision.constantInstructionResult c
        (.NoEllipses, available) i = some iit →
      iit.1.INS = (.NoEllipses, need) →
      ∀ t ∈ need, CandidateValMatch.InTableVal c t) :
    StepCalls c available i pushed
      start middle₁ middle₂ middle₃ finish ↔
      constantStepResult c available i = some pushed ∧
      middle₁ = start ∧ middle₂ = start ∧
      middle₃ = start ∧ finish = start := by
  constructor
  · rintro ⟨hallowed, iit, popped, hinstr, hinit, hpop, hpush⟩
    obtain ⟨hi, hm₁⟩ :=
      (ConstInstrDecision.constant_instruction_result_iff
        c (.NoEllipses, available) i iit start middle₁).2
        ⟨hallowed, hinstr⟩
    obtain ⟨need, hins, _⟩ :=
      ConstInstrDecision.constant_instruction_input_shape
        c (.NoEllipses, available) i iit hi
    have hm₂ :=
      ((LocalInitValidation.init_locals_success_iff_result
        c iit.2 c middle₁ middle₂).1 hinit).2
    have hpop' : SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.Call.«$pop» c
            (.NoEllipses, need) (.NoEllipses, available)⟩)
        middle₂ (.success (.of popped)) middle₃ := by
      simpa only [hins] using hpop
    obtain ⟨hp, hm₃⟩ :=
      (PopNoEllipsesDecision.pop_result_iff_any_counters
        c need available popped middle₂ middle₃ hready
        (hinputs iit need hi hins) havailable).2 hpop'
    obtain ⟨hpushResult, hm₄⟩ :=
      (PushValidation.push_success_iff_result
        c iit.1.OUTS popped pushed middle₃ finish).1 hpush
    have hstep :=
      (constant_step_result_iff_components
        c available i pushed).2
        ⟨iit, need, popped, hi, hins, hp, hpushResult⟩
    exact ⟨hstep, hm₁, hm₂.trans hm₁,
      hm₃.trans (hm₂.trans hm₁),
      hm₄.trans (hm₃.trans (hm₂.trans hm₁))⟩
  · rintro ⟨hstep, rfl, rfl, rfl, rfl⟩
    exact (constant_step_result_iff_calls c available i pushed finish
      hready havailable hinputs).1 hstep

end properties.wasm_module_ok.ConstStepDecision
