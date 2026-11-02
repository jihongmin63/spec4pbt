import properties.wasm_module_not_ok.DeftypeSubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateSubstList

open properties.wasm_module_not_ok.Rejection

/-- Compute the ordered substitutions used by the first recursive-group pass. -/
def substList (c : SpecTec.context) :
    List SpecTec.deftype → Option (List SpecTec.deftype)
  | [] => some []
  | dt :: rest => do
      let dt' ← substDeftypeResult dt c.TYPES
      let rest' ← substList c rest
      some (dt' :: rest')

/-- The translated iterator has exactly the result of the safe list computation,
including an ordered unmatch when either the head or tail substitution fails. -/
theorem subst_list_total (c : SpecTec.context)
    (rolled : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨List SpecTec.deftype,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:2» c rolled⟩)
      n (optionOutcome (substList c rolled)) n := by
  induction rolled with
  | nil =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«Rectype_ok:rule:iter:2_clauses» c []) ())
        n (.success (.of ([] : List SpecTec.deftype))) n
      apply SpecTecExecution.firstSuccess_cons_success
      exact SpecTecExecution.Eval.pure []
  | cons dt rest ih =>
      have hhead := subst_deftype_of_total dt c.TYPES n
      cases hdt : substDeftypeResult dt c.TYPES with
      | none =>
          have hresult : substList c (dt :: rest) = none := by
            simp [substList, hdt]
          rw [hresult]
          simp only [optionOutcome]
          apply SpecTecExecution.Eval.call
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTecExecution.firstSuccess
              (SpecTec.«Rectype_ok:rule:iter:2_clauses» c (dt :: rest)) ())
            n .unmatch n
          apply SpecTecExecution.firstSuccess_cons_unmatch
          · exact SpecTecExecution.Eval.unmatch
          · apply SpecTecExecution.firstSuccess_cons_unmatch
            · unfold SpecTec.«Rectype_ok:rule:iter:2:clause:1»
              apply SpecTecExecution.Eval.bind_unmatch
              simpa [optionOutcome, hdt] using hhead
            · exact SpecTecExecution.firstSuccess_nil () n
      | some dt' =>
          have hhead' : SpecTecExecution.Eval SpecTec.specTecProgram
              (.call ⟨SpecTec.deftype,
                SpecTec.SpecTecCall.«$subst_deftype»
                  (List SpecTec.deftype) c.TYPES
                  SpecTec.SpecTecCall.«$subst_of» dt⟩)
              n (.success (.of dt')) n := by
            simpa [optionOutcome, hdt] using hhead
          cases hrest : substList c rest with
          | none =>
              have hresult : substList c (dt :: rest) = none := by
                simp [substList, hdt, hrest]
              rw [hresult]
              simp only [optionOutcome]
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTecExecution.firstSuccess
                  (SpecTec.«Rectype_ok:rule:iter:2_clauses» c (dt :: rest)) ())
                n .unmatch n
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · exact SpecTecExecution.Eval.unmatch
              · apply SpecTecExecution.firstSuccess_cons_unmatch
                · unfold SpecTec.«Rectype_ok:rule:iter:2:clause:1»
                  apply SpecTecExecution.Eval.bind_success hhead'
                  apply SpecTecExecution.Eval.bind_unmatch
                  simpa [optionOutcome, hrest] using ih
                · exact SpecTecExecution.firstSuccess_nil () n
          | some rest' =>
              have hresult : substList c (dt :: rest) = some (dt' :: rest') := by
                simp [substList, hdt, hrest]
              rw [hresult]
              simp only [optionOutcome]
              apply SpecTecExecution.Eval.call
              change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTecExecution.firstSuccess
                  (SpecTec.«Rectype_ok:rule:iter:2_clauses» c (dt :: rest)) ())
                n (.success (.of (dt' :: rest'))) n
              apply SpecTecExecution.firstSuccess_cons_unmatch
              · exact SpecTecExecution.Eval.unmatch
              · apply SpecTecExecution.firstSuccess_cons_success
                unfold SpecTec.«Rectype_ok:rule:iter:2:clause:1»
                apply SpecTecExecution.Eval.bind_success hhead'
                apply SpecTecExecution.Eval.bind_success
                  (by simpa [optionOutcome, hrest] using ih)
                exact SpecTecExecution.Eval.pure (dt' :: rest')

end properties.wasm_module_ok.CandidateSubstList
