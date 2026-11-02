import properties.wasm_module_ok.ConstInstrDecision
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstFrame
open SpecTec properties.wasm_module_ok

private theorem peek_suffix (pref suffix : List valtype) (hn : suffix≠[]) :
    PeekDecision.peekResult 0 (.NoEllipses,pref++suffix)=
      PeekDecision.peekResult 0 (.NoEllipses,suffix) := by
  have hl : 0<suffix.reverse.length := by simpa using List.length_pos_iff.2 hn
  simp only [PeekDecision.peekResult,List.reverse_append,List.getElem?_append_left hl]

/-- Replacing an older stack pref preserves every constant instruction's
original effect, including EXTERN.CONVERT's actual nullability peek. -/
theorem instruction_suffix (c : context) (pref suffix newer : List valtype)
    (i : instr) (iit : inferinstrtype)
    (h : ConstInstrDecision.constantInstructionResult c (.NoEllipses,pref++suffix) i=some iit)
    (hl : iit.1.INS.2.length≤suffix.length) :
    ConstInstrDecision.constantInstructionResult c (.NoEllipses,newer++suffix) i=some iit := by
  unfold ConstInstrDecision.constantInstructionResult at h ⊢
  split at h
  next ha =>
    rw [if_pos ha]
    cases i <;> try exact h
    case «EXTERN.CONVERT» op =>
      have hn : suffix≠[] := by
        intro he
        cases hp : PeekRefDecision.peekRefResult
          (PeekDecision.peekResult 0 (.NoEllipses,pref++suffix)) with
        | none => simp [ConstInstrDecision.externConvertResult,hp] at h
        | some rt =>
          rcases rt with ⟨nu,ht⟩
          simp only [ConstInstrDecision.externConvertResult,hp,Option.some.injEq] at h
          subst iit
          simp [he] at hl
      simpa only [ConstInstrDecision.externConvertResult,peek_suffix newer suffix hn,
        peek_suffix pref suffix hn] using h
    case «STRUCT.NEW» x op => cases op <;> exact h
    case «ARRAY.NEW» x op => cases op <;> exact h
  next ha => simp at h

/-- The frame theorem is stated on actual original calls, not the classifier.
The classifier above is used only inside this proof. -/
theorem original_instruction_suffix (c : context) (pref suffix newer : List valtype)
    (i : instr) (iit : inferinstrtype) (start finish n : Nat)
    (hsyntax : ConstAdditionalSyntaxValidation.Syntax c i)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c (.NoEllipses,pref++suffix) i⟩)
      start (.success (.of iit)) finish)
    (hl : iit.1.INS.2.length≤suffix.length) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c (.NoEllipses,newer++suffix) i⟩)
      n (.success (.of iit)) n := by
  have hs := (ConstSyntaxDecision.syntaxAllowed_iff c i).2 hsyntax
  have hv := ((ConstInstrDecision.constant_instruction_result_iff c _ i iit start finish).2 ⟨hs,h⟩).1
  exact ((ConstInstrDecision.constant_instruction_result_iff c _ i iit n n).1
    ⟨instruction_suffix c pref suffix newer i iit hv hl,rfl⟩).2

#print axioms original_instruction_suffix
end properties.wasm_module_ok.ConstructiveConstFrame
