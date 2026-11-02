import properties.wasm_module_ok.SubtypeHeadListValidation
import properties.wasm_module_ok.StrtypeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.SubtypeValidation

def subtypeValid (c : SpecTec.context) : SpecTec.subtype → Bool
  | .SubT _ hts st =>
      decide (hts.length ≤ 1) &&
        SubtypeHeadListValidation.allHeaptypesValid c hts &&
        StrtypeValidation.strtypeValid c st

theorem subtype_success_iff_calls
    (c : SpecTec.context) (fin : SpecTec.final)
    (hts : List SpecTec.heaptype) (st : SpecTec.strtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_ok c (.SubT fin hts st)⟩)
      n (.success (.of ())) finish ↔
    hts.length ≤ 1 ∧
      ∃ middle : Nat,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit,
            SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c hts⟩)
          n (.success (.of ())) middle ∧
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit, SpecTec.SpecTecCall.Strtype_ok c st⟩)
          middle (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.firstSuccess_success_iff
          (SpecTec.Subtype_ok_clauses c (.SubT fin hts st)) ()
          n (.of ()) finish).1 hbody
      unfold SpecTec.Subtype_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«Subtype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard hrest =>
          cases hguard with
          | guard_true hbound =>
            cases hrest with
            | bind_success hlist htail =>
              rename_i middle _
              cases htail with
              | bind_success hstr hpure =>
                cases hpure
                exact ⟨hbound, middle, hlist, hstr⟩
      | next _ hnone => cases hnone
  · rintro ⟨hbound, middle, hlist, hstr⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Subtype_ok_clauses c (.SubT fin hts st)) ())
      n (.success (.of ())) finish
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Subtype_ok:clause:0» c (.SubT fin hts st))
      n (.success (.of ())) finish
    unfold SpecTec.«Subtype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hbound
    · apply SpecTecExecution.Eval.bind_success hlist
      apply SpecTecExecution.Eval.bind_success hstr
      exact SpecTecExecution.Eval.pure ()

theorem subtype_success_iff_valid
    (c : SpecTec.context) (sub : SpecTec.subtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_ok c sub⟩)
      n (.success (.of ())) finish ↔
    subtypeValid c sub = true ∧ finish = n := by
  cases sub with
  | SubT fin hts st =>
    rw [subtype_success_iff_calls]
    constructor
    · rintro ⟨hbound, middle, hlist, hstr⟩
      obtain ⟨hvalidList, hmiddle⟩ :=
        (SubtypeHeadListValidation.iter_success_iff_valid
          c hts n middle).1 hlist
      obtain ⟨hvalidSt, hsupply⟩ :=
        (StrtypeValidation.strtype_success_iff_valid
          c st middle finish).1 hstr
      exact ⟨by simp [subtypeValid, hbound, hvalidList, hvalidSt],
        hmiddle ▸ hsupply⟩
    · rintro ⟨hvalid, rfl⟩
      have hparts : (hts.length ≤ 1 ∧
          SubtypeHeadListValidation.allHeaptypesValid c hts = true) ∧
          StrtypeValidation.strtypeValid c st = true := by
        simpa [subtypeValid] using hvalid
      exact ⟨hparts.1.1, finish,
        (SubtypeHeadListValidation.iter_success_iff_valid
          c hts finish finish).2 ⟨hparts.1.2, rfl⟩,
        (StrtypeValidation.strtype_success_iff_valid
          c st finish finish).2 ⟨hparts.2, rfl⟩⟩

end properties.wasm_module_ok.SubtypeValidation
