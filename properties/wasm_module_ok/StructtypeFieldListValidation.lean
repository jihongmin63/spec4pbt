import properties.wasm_module_ok.FieldtypeValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.StructtypeFieldListValidation

/-- The structural type pass checks every field without recursive matching. -/
def allFieldsValid (c : SpecTec.context) :
    List SpecTec.fieldtype → Bool
  | [] => true
  | ft :: fields => FieldtypeValidation.fieldtypeValid c ft &&
      allFieldsValid c fields

theorem iter_nil_success (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Structtype_ok:rule:iter:0» c []⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«Structtype_ok:rule:iter:0_clauses» c []))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_success
  exact SpecTecExecution.Eval.pure ()

theorem iter_cons_success_iff
    (c : SpecTec.context) (ft : SpecTec.fieldtype)
    (fields : List SpecTec.fieldtype) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Structtype_ok:rule:iter:0» c (ft :: fields)⟩)
      n (.success (.of ())) finish ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Fieldtype_ok c ft⟩)
        n (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit,
          SpecTec.Call.«Structtype_ok:rule:iter:0» c fields⟩)
        middle (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse
          (SpecTec.«Structtype_ok:rule:iter:0:clause:0» c (ft :: fields))
          (fun _ => SpecTecExecution.tryClauses
            [
              SpecTec.«Structtype_ok:rule:iter:0:clause:1» c (ft :: fields)]))
        n (.success (.of ())) finish at hbody
      cases hbody with
      | orElse_success hfirst =>
        change SpecTecExecution.Eval SpecTec.Body
          (.unmatch) n (.success (.of ())) finish at hfirst
        cases hfirst
      | orElse_unmatch hfailedSupply htail =>
        restore_supply hfailedSupply at htail
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse
            (SpecTec.«Structtype_ok:rule:iter:0:clause:1» c (ft :: fields))
            (fun _ => .unmatch))
          n (.success (.of ())) finish at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Structtype_ok:rule:iter:0:clause:1» at hsecond
          cases hsecond with
          | bind_success hhead htail =>
            rename_i middle value
            cases value
            cases htail with
            | bind_success hrest hpure =>
              rename_i _ valueRest
              cases valueRest
              cases hpure
              exact ⟨middle, hhead, hrest⟩
        | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  · rintro ⟨middle, hhead, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«Structtype_ok:rule:iter:0_clauses» c (ft :: fields)))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Structtype_ok:rule:iter:0:clause:0» c (ft :: fields))
        n .unmatch n
      exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Structtype_ok:rule:iter:0:clause:1» c (ft :: fields))
        n (.success (.of ())) finish
      unfold SpecTec.«Structtype_ok:rule:iter:0:clause:1»
      apply SpecTecExecution.Eval.bind_success hhead
      apply SpecTecExecution.Eval.bind_success hrest
      exact SpecTecExecution.Eval.pure ()

theorem iter_success_iff_valid
    (c : SpecTec.context) (fields : List SpecTec.fieldtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Structtype_ok:rule:iter:0» c fields⟩)
      n (.success (.of ())) finish ↔
    allFieldsValid c fields = true ∧ finish = n := by
  induction fields generalizing n finish with
  | nil =>
    constructor
    · intro h
      obtain ⟨_, hsupply⟩ :=
        properties.wasm_module_ok.Execution.eval_deterministic h
          (iter_nil_success c n)
      exact ⟨rfl, hsupply⟩
    · rintro ⟨_, rfl⟩
      exact iter_nil_success c finish
  | cons ft fields ih =>
    constructor
    · intro h
      obtain ⟨middle, hhead, hrest⟩ :=
        (iter_cons_success_iff c ft fields n finish).1 h
      obtain ⟨hvalid, hmiddle⟩ :=
        (FieldtypeValidation.fieldtype_success_iff_valid
          c ft n middle).1 hhead
      obtain ⟨hvalidRest, hsupply⟩ :=
        (ih middle finish).1 hrest
      subst middle
      exact ⟨by simp [allFieldsValid, hvalid, hvalidRest], hsupply⟩
    · rintro ⟨hall, rfl⟩
      have hparts : FieldtypeValidation.fieldtypeValid c ft = true ∧
          allFieldsValid c fields = true := by
        simpa [allFieldsValid] using hall
      obtain ⟨hhead, hrest⟩ := hparts
      apply (iter_cons_success_iff c ft fields finish finish).2
      exact ⟨finish,
        (FieldtypeValidation.fieldtype_success_iff_valid
          c ft finish finish).2 ⟨hhead, rfl⟩,
        (ih finish finish).2 ⟨hrest, rfl⟩⟩

end properties.wasm_module_ok.StructtypeFieldListValidation
