import properties.wasm_module_ok.StartValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.FunctypeProjectionValidation

def functypeProjection : SpecTec.strtype → Option SpecTec.functype
  | .DefFuncT ft => some ft
  | _ => none

def projectionOutcome (st : SpecTec.strtype) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match functypeProjection st with
  | none => .unmatch
  | some ft => .success (.of ft)

theorem projection_total (st : SpecTec.strtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.functype,
        SpecTec.SpecTecCall.«$functype_of_strtype» st⟩)
      n (projectionOutcome st) n := by
  cases st with
  | DefFuncT ft =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$functype_of_strtype_clauses» (.DefFuncT ft)) ())
      n (projectionOutcome (.DefFuncT ft)) n
    simp only [projectionOutcome, functypeProjection]
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$functype_of_strtype:clause:0» (.DefFuncT ft))
      n (.success (.of ft)) n
    unfold SpecTec.«$functype_of_strtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · exact SpecTecExecution.Eval.pure ft
  | DefStructT st =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$functype_of_strtype_clauses» (.DefStructT st)) ())
      n (projectionOutcome (.DefStructT st)) n
    simp only [projectionOutcome, functypeProjection]
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$functype_of_strtype:clause:0» (.DefStructT st))
        n .unmatch n
      unfold SpecTec.«$functype_of_strtype:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      change ¬ false = true
      decide
    · exact SpecTecExecution.firstSuccess_nil () n
  | DefArrayT arr =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$functype_of_strtype_clauses» (.DefArrayT arr)) ())
      n (projectionOutcome (.DefArrayT arr)) n
    simp only [projectionOutcome, functypeProjection]
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$functype_of_strtype:clause:0» (.DefArrayT arr))
        n .unmatch n
      unfold SpecTec.«$functype_of_strtype:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      change ¬ false = true
      decide
    · exact SpecTecExecution.firstSuccess_nil () n

end properties.wasm_module_ok.FunctypeProjectionValidation
