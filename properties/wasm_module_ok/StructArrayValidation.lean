import properties.wasm_module_ok.StructtypeFieldListValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.StructArrayValidation

def structtypeValid (c : SpecTec.context) : SpecTec.structtype → Bool
  | .StructT fields => StructtypeFieldListValidation.allFieldsValid c fields

def arraytypeValid (c : SpecTec.context) : SpecTec.arraytype → Bool
  | .ArrayT ft => FieldtypeValidation.fieldtypeValid c ft

theorem structtype_success_iff_iter
    (c : SpecTec.context) (fields : List SpecTec.fieldtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Structtype_ok c (.StructT fields)⟩)
      n (.success (.of ())) finish ↔
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Structtype_ok:rule:iter:0» c fields⟩)
      n (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.tryClauses_success_iff
          (SpecTec.Structtype_ok_clauses c (.StructT fields))
          n (.of ()) finish).1 hbody
      unfold SpecTec.Structtype_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«Structtype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hiter hpure =>
          cases hpure
          exact hiter
      | next _ hnone => cases hnone
  · intro hiter
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Structtype_ok_clauses c (.StructT fields)))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Structtype_ok:clause:0» c (.StructT fields))
      n (.success (.of ())) finish
    unfold SpecTec.«Structtype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success hiter
    exact SpecTecExecution.Eval.pure ()

theorem structtype_success_iff_valid
    (c : SpecTec.context) (st : SpecTec.structtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Structtype_ok c st⟩)
      n (.success (.of ())) finish ↔
    structtypeValid c st = true ∧ finish = n := by
  cases st with
  | StructT fields =>
    rw [structtype_success_iff_iter,
      StructtypeFieldListValidation.iter_success_iff_valid]
    rfl

theorem arraytype_success_iff_field
    (c : SpecTec.context) (ft : SpecTec.fieldtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Arraytype_ok c (.ArrayT ft)⟩)
      n (.success (.of ())) finish ↔
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Fieldtype_ok c ft⟩)
      n (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.tryClauses_success_iff
          (SpecTec.Arraytype_ok_clauses c (.ArrayT ft))
          n (.of ()) finish).1 hbody
      unfold SpecTec.Arraytype_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«Arraytype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hfield hpure =>
          cases hpure
          exact hfield
      | next _ hnone => cases hnone
  · intro hfield
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Arraytype_ok_clauses c (.ArrayT ft)))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Arraytype_ok:clause:0» c (.ArrayT ft))
      n (.success (.of ())) finish
    unfold SpecTec.«Arraytype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success hfield
    exact SpecTecExecution.Eval.pure ()

theorem arraytype_success_iff_valid
    (c : SpecTec.context) (arr : SpecTec.arraytype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Arraytype_ok c arr⟩)
      n (.success (.of ())) finish ↔
    arraytypeValid c arr = true ∧ finish = n := by
  cases arr with
  | ArrayT ft =>
    rw [arraytype_success_iff_field,
      FieldtypeValidation.fieldtype_success_iff_valid]
    rfl

end properties.wasm_module_ok.StructArrayValidation
