import properties.wasm_module_ok.FunctypeValidation
import properties.wasm_module_ok.StructArrayValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.StrtypeValidation

def strtypeValid (c : SpecTec.context) : SpecTec.strtype → Bool
  | .DefStructT st => StructArrayValidation.structtypeValid c st
  | .DefArrayT arr => StructArrayValidation.arraytypeValid c arr
  | .DefFuncT ft => FunctypeValidation.functypeValid c ft

theorem struct_success_iff_child
    (c : SpecTec.context) (st : SpecTec.structtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Strtype_ok c (.DefStructT st)⟩)
      n (.success (.of ())) finish ↔
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Structtype_ok c st⟩)
      n (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (properties.wasm_module_ok.Execution.tryClauses_success_iff
          (SpecTec.Strtype_ok_clauses c (.DefStructT st))
          n (.of ()) finish).1 hbody
      unfold SpecTec.Strtype_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«Strtype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard htail =>
          cases hguard
          cases htail with
          | bind_success hstruct hpure =>
            cases hpure
            exact hstruct
      | next _ hrest =>
        cases hrest with
        | here hsecond =>
          unfold SpecTec.«Strtype_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond =>
              simp [SpecTec.«exec:match:strtype:DefArrayT»] at hcond
        | next _ hlast =>
          cases hlast with
          | here hthird =>
            unfold SpecTec.«Strtype_ok:clause:2» at hthird
            cases hthird with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond =>
                simp [SpecTec.«exec:match:strtype:DefFuncT»] at hcond
          | next _ hnone => cases hnone
  · intro hstruct
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Strtype_ok_clauses c (.DefStructT st)))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Strtype_ok:clause:0» c (.DefStructT st))
      n (.success (.of ())) finish
    unfold SpecTec.«Strtype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success hstruct
      exact SpecTecExecution.Eval.pure ()

theorem array_success_iff_child
    (c : SpecTec.context) (arr : SpecTec.arraytype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Strtype_ok c (.DefArrayT arr)⟩)
      n (.success (.of ())) finish ↔
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Arraytype_ok c arr⟩)
      n (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (properties.wasm_module_ok.Execution.tryClauses_success_iff
          (SpecTec.Strtype_ok_clauses c (.DefArrayT arr))
          n (.of ()) finish).1 hbody
      unfold SpecTec.Strtype_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«Strtype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond =>
            simp [SpecTec.«exec:match:strtype:DefStructT»] at hcond
      | next _ hrest =>
        cases hrest with
        | here hsecond =>
          unfold SpecTec.«Strtype_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard htail =>
            cases hguard
            cases htail with
            | bind_success harray hpure =>
              cases hpure
              exact harray
        | next _ hlast =>
          cases hlast with
          | here hthird =>
            unfold SpecTec.«Strtype_ok:clause:2» at hthird
            cases hthird with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond =>
                simp [SpecTec.«exec:match:strtype:DefFuncT»] at hcond
          | next _ hnone => cases hnone
  · intro harray
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Strtype_ok_clauses c (.DefArrayT arr)))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Strtype_ok:clause:0» c (.DefArrayT arr))
        n .unmatch n
      unfold SpecTec.«Strtype_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp [SpecTec.«exec:match:strtype:DefStructT»]
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Strtype_ok:clause:1» c (.DefArrayT arr))
        n (.success (.of ())) finish
      unfold SpecTec.«Strtype_ok:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success harray
        exact SpecTecExecution.Eval.pure ()

theorem func_success_iff_child
    (c : SpecTec.context) (ft : SpecTec.functype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Strtype_ok c (.DefFuncT ft)⟩)
      n (.success (.of ())) finish ↔
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Functype_ok c ft⟩)
      n (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (properties.wasm_module_ok.Execution.tryClauses_success_iff
          (SpecTec.Strtype_ok_clauses c (.DefFuncT ft))
          n (.of ()) finish).1 hbody
      unfold SpecTec.Strtype_ok_clauses at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«Strtype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond =>
            simp [SpecTec.«exec:match:strtype:DefStructT»] at hcond
      | next _ hrest =>
        cases hrest with
        | here hsecond =>
          unfold SpecTec.«Strtype_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond =>
              simp [SpecTec.«exec:match:strtype:DefArrayT»] at hcond
        | next _ hlast =>
          cases hlast with
          | here hthird =>
            unfold SpecTec.«Strtype_ok:clause:2» at hthird
            cases hthird with
            | bind_success hguard htail =>
              cases hguard
              cases htail with
              | bind_success hfunc hpure =>
                cases hpure
                exact hfunc
          | next _ hnone => cases hnone
  · intro hfunc
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Strtype_ok_clauses c (.DefFuncT ft)))
      n (.success (.of ())) finish
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Strtype_ok:clause:0» c (.DefFuncT ft))
        n .unmatch n
      unfold SpecTec.«Strtype_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp [SpecTec.«exec:match:strtype:DefStructT»]
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Strtype_ok:clause:1» c (.DefFuncT ft))
          n .unmatch n
        unfold SpecTec.«Strtype_ok:clause:1»
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp [SpecTec.«exec:match:strtype:DefArrayT»]
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Strtype_ok:clause:2» c (.DefFuncT ft))
          n (.success (.of ())) finish
        unfold SpecTec.«Strtype_ok:clause:2»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success hfunc
          exact SpecTecExecution.Eval.pure ()

theorem strtype_success_iff_valid
    (c : SpecTec.context) (st : SpecTec.strtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Strtype_ok c st⟩)
      n (.success (.of ())) finish ↔
    strtypeValid c st = true ∧ finish = n := by
  cases st with
  | DefStructT struct =>
    rw [struct_success_iff_child,
      StructArrayValidation.structtype_success_iff_valid]
    rfl
  | DefArrayT arr =>
    rw [array_success_iff_child,
      StructArrayValidation.arraytype_success_iff_valid]
    rfl
  | DefFuncT ft =>
    rw [func_success_iff_child,
      FunctypeValidation.functype_success_iff_valid]
    rfl

end properties.wasm_module_ok.StrtypeValidation
