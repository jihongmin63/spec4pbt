import properties.wasm_module_ok.ResulttypeListValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.FunctypeValidation

def resulttypeValid (c : SpecTec.context) (ts : SpecTec.resulttype) : Bool :=
  ResulttypeListValidation.allValtypesValid c ts

def functypeValid (c : SpecTec.context) : SpecTec.functype → Bool
  | .FuncT inputs outputs =>
      resulttypeValid c inputs && resulttypeValid c outputs

theorem resulttype_success_iff_iter
    (c : SpecTec.context) (ts : SpecTec.resulttype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Resulttype_ok c ts⟩)
      n (.success (.of ())) finish ↔
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Resulttype_ok:rule:iter:0» c ts⟩)
      n (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.tryClauses_success_iff
          (SpecTec.Resulttype_ok_clauses c ts)
          n (.of ()) finish).1 hbody
      unfold SpecTec.Resulttype_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«Resulttype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hiter hpure =>
          cases hpure
          exact hiter
      | next _ hnone => cases hnone
  · intro hiter
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Resulttype_ok_clauses c ts))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Resulttype_ok:clause:0» c ts)
      n (.success (.of ())) finish
    unfold SpecTec.«Resulttype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success hiter
    exact SpecTecExecution.Eval.pure ()

theorem resulttype_success_iff_valid
    (c : SpecTec.context) (ts : SpecTec.resulttype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Resulttype_ok c ts⟩)
      n (.success (.of ())) finish ↔
    resulttypeValid c ts = true ∧ finish = n := by
  rw [resulttype_success_iff_iter,
    ResulttypeListValidation.iter_success_iff_valid]
  rfl

theorem functype_success_iff_results
    (c : SpecTec.context) (inputs outputs : SpecTec.resulttype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Functype_ok c (.FuncT inputs outputs)⟩)
      n (.success (.of ())) finish ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Resulttype_ok c inputs⟩)
        n (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Resulttype_ok c outputs⟩)
        middle (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.tryClauses_success_iff
          (SpecTec.Functype_ok_clauses c (.FuncT inputs outputs))
          n (.of ()) finish).1 hbody
      unfold SpecTec.Functype_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«Functype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hinputs hrest =>
          rename_i middle _
          cases hrest with
          | bind_success houtputs hpure =>
            cases hpure
            exact ⟨middle, hinputs, houtputs⟩
      | next _ hnone => cases hnone
  · rintro ⟨middle, hinputs, houtputs⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Functype_ok_clauses c (.FuncT inputs outputs)))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Functype_ok:clause:0» c (.FuncT inputs outputs))
      n (.success (.of ())) finish
    unfold SpecTec.«Functype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success hinputs
    apply SpecTecExecution.Eval.bind_success houtputs
    exact SpecTecExecution.Eval.pure ()

theorem functype_success_iff_valid
    (c : SpecTec.context) (ft : SpecTec.functype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Functype_ok c ft⟩)
      n (.success (.of ())) finish ↔
    functypeValid c ft = true ∧ finish = n := by
  cases ft with
  | FuncT inputs outputs =>
    rw [functype_success_iff_results]
    constructor
    · rintro ⟨middle, hinputs, houtputs⟩
      obtain ⟨hvalidInputs, hmiddle⟩ :=
        (resulttype_success_iff_valid c inputs n middle).1 hinputs
      obtain ⟨hvalidOutputs, hsupply⟩ :=
        (resulttype_success_iff_valid c outputs middle finish).1 houtputs
      exact ⟨by simp [functypeValid, hvalidInputs, hvalidOutputs],
        hmiddle ▸ hsupply⟩
    · rintro ⟨hvalid, rfl⟩
      have hparts : resulttypeValid c inputs = true ∧
          resulttypeValid c outputs = true := by
        simpa [functypeValid] using hvalid
      exact ⟨finish,
        (resulttype_success_iff_valid c inputs finish finish).2
          ⟨hparts.1, rfl⟩,
        (resulttype_success_iff_valid c outputs finish finish).2
          ⟨hparts.2, rfl⟩⟩

end properties.wasm_module_ok.FunctypeValidation
