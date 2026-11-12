import properties.wasm_module_not_ok.StructtypeValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def strtypeValid (c : SpecTec.context) : SpecTec.strtype → Bool
  | .DefStructT st => structtypeValid c st
  | .DefArrayT arrayTy => arraytypeValid c arrayTy
  | .DefFuncT ft => functypeValid c ft

theorem strtype_struct_success_iff_valid (c : SpecTec.context)
    (st : SpecTec.structtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Strtype_ok c (.DefStructT st)⟩)
      start (.success (.of ())) finalSupply ↔
    strtypeValid c (.DefStructT st) = true ∧ finalSupply = start := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Strtype_ok:clause:0» c (.DefStructT st))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«Strtype_ok:clause:1» c (.DefStructT st),
             fun _ => SpecTec.«Strtype_ok:clause:2» c (.DefStructT st)] ()))
        start (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Strtype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard hrest =>
          cases hguard with
          | guard_true _ =>
            cases hrest with
            | bind_success hstruct hpure =>
              cases hpure with
              | pure =>
                simpa [strtypeValid] using
                  (structtype_ok_success_iff_valid c st start finalSupply).1 hstruct
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Strtype_ok:clause:1» c (.DefStructT st))
            (fun _ => SpecTecExecution.firstSuccess
              [fun _ => SpecTec.«Strtype_ok:clause:2» c (.DefStructT st)] ()))
          start (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Strtype_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond =>
              simp [SpecTec.«exec:match:strtype:DefArrayT»] at hcond
        | orElse_unmatch _ hlast =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Strtype_ok:clause:2» c (.DefStructT st))
              (fun _ => .unmatch))
            start (.success (.of ())) finalSupply at hlast
          cases hlast with
          | orElse_success hthird =>
            unfold SpecTec.«Strtype_ok:clause:2» at hthird
            cases hthird with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond =>
                simp [SpecTec.«exec:match:strtype:DefFuncT»] at hcond
          | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨hvalid, rfl⟩
    have hstruct :=
      (structtype_ok_success_iff_valid c st finalSupply finalSupply).2
        ⟨by simpa [strtypeValid] using hvalid, rfl⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Strtype_ok_clauses c (.DefStructT st)) ())
      finalSupply (.success (.of ())) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Strtype_ok:clause:0» c (.DefStructT st))
      finalSupply (.success (.of ())) finalSupply
    unfold SpecTec.«Strtype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:strtype:DefStructT»])
    · apply SpecTecExecution.Eval.bind_success hstruct
      exact SpecTecExecution.Eval.pure ()

theorem strtype_array_success_iff_valid (c : SpecTec.context)
    (arrayTy : SpecTec.arraytype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Strtype_ok c (.DefArrayT arrayTy)⟩)
      start (.success (.of ())) finalSupply ↔
    strtypeValid c (.DefArrayT arrayTy) = true ∧ finalSupply = start := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Strtype_ok:clause:0» c (.DefArrayT arrayTy))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«Strtype_ok:clause:1» c (.DefArrayT arrayTy),
             fun _ => SpecTec.«Strtype_ok:clause:2» c (.DefArrayT arrayTy)] ()))
        start (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Strtype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond =>
            simp [SpecTec.«exec:match:strtype:DefStructT»] at hcond
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Strtype_ok:clause:1» c (.DefArrayT arrayTy))
            (fun _ => SpecTecExecution.firstSuccess
              [fun _ => SpecTec.«Strtype_ok:clause:2» c (.DefArrayT arrayTy)] ()))
          start (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Strtype_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard hrest =>
            cases hguard with
            | guard_true _ =>
              cases hrest with
              | bind_success harray hpure =>
                cases hpure with
                | pure =>
                  simpa [strtypeValid] using
                    (arraytype_ok_success_iff_valid c arrayTy start finalSupply).1
                      harray
        | orElse_unmatch _ hlast =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Strtype_ok:clause:2» c (.DefArrayT arrayTy))
              (fun _ => .unmatch))
            start (.success (.of ())) finalSupply at hlast
          cases hlast with
          | orElse_success hthird =>
            unfold SpecTec.«Strtype_ok:clause:2» at hthird
            cases hthird with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond =>
                simp [SpecTec.«exec:match:strtype:DefFuncT»] at hcond
          | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨hvalid, rfl⟩
    have harray :=
      (arraytype_ok_success_iff_valid c arrayTy finalSupply finalSupply).2
        ⟨by simpa [strtypeValid] using hvalid, rfl⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Strtype_ok_clauses c (.DefArrayT arrayTy)) ())
      finalSupply (.success (.of ())) finalSupply
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Strtype_ok:clause:0» c (.DefArrayT arrayTy))
        finalSupply .unmatch finalSupply
      unfold SpecTec.«Strtype_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:strtype:DefStructT»])
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Strtype_ok:clause:1» c (.DefArrayT arrayTy))
        finalSupply (.success (.of ())) finalSupply
      unfold SpecTec.«Strtype_ok:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true
          (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
      · apply SpecTecExecution.Eval.bind_success harray
        exact SpecTecExecution.Eval.pure ()

theorem strtype_func_success_iff_valid (c : SpecTec.context)
    (ft : SpecTec.functype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Strtype_ok c (.DefFuncT ft)⟩)
      start (.success (.of ())) finalSupply ↔
    strtypeValid c (.DefFuncT ft) = true ∧ finalSupply = start := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Strtype_ok:clause:0» c (.DefFuncT ft))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«Strtype_ok:clause:1» c (.DefFuncT ft),
             fun _ => SpecTec.«Strtype_ok:clause:2» c (.DefFuncT ft)] ()))
        start (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Strtype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond =>
            simp [SpecTec.«exec:match:strtype:DefStructT»] at hcond
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Strtype_ok:clause:1» c (.DefFuncT ft))
            (fun _ => SpecTecExecution.firstSuccess
              [fun _ => SpecTec.«Strtype_ok:clause:2» c (.DefFuncT ft)] ()))
          start (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Strtype_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond =>
              simp [SpecTec.«exec:match:strtype:DefArrayT»] at hcond
        | orElse_unmatch _ hlast =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Strtype_ok:clause:2» c (.DefFuncT ft))
              (fun _ => .unmatch))
            start (.success (.of ())) finalSupply at hlast
          cases hlast with
          | orElse_success hthird =>
            unfold SpecTec.«Strtype_ok:clause:2» at hthird
            cases hthird with
            | bind_success hguard hrest =>
              cases hguard with
              | guard_true _ =>
                cases hrest with
                | bind_success hfun hpure =>
                  cases hpure with
                  | pure =>
                    simpa [strtypeValid] using
                      (functype_ok_success_iff_valid c ft start finalSupply).1
                        hfun
          | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨hvalid, rfl⟩
    have hfun :=
      (functype_ok_success_iff_valid c ft finalSupply finalSupply).2
        ⟨by simpa [strtypeValid] using hvalid, rfl⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Strtype_ok_clauses c (.DefFuncT ft)) ())
      finalSupply (.success (.of ())) finalSupply
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Strtype_ok:clause:0» c (.DefFuncT ft))
        finalSupply .unmatch finalSupply
      unfold SpecTec.«Strtype_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:strtype:DefStructT»])
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Strtype_ok:clause:1» c (.DefFuncT ft))
          finalSupply .unmatch finalSupply
        unfold SpecTec.«Strtype_ok:clause:1»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:strtype:DefArrayT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Strtype_ok:clause:2» c (.DefFuncT ft))
          finalSupply (.success (.of ())) finalSupply
        unfold SpecTec.«Strtype_ok:clause:2»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true
            (by simp [SpecTec.«exec:match:strtype:DefFuncT»])
        · apply SpecTecExecution.Eval.bind_success hfun
          exact SpecTecExecution.Eval.pure ()

theorem strtype_ok_success_iff_valid (c : SpecTec.context)
    (strt : SpecTec.strtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Strtype_ok c strt⟩)
      start (.success (.of ())) finalSupply ↔
    strtypeValid c strt = true ∧ finalSupply = start := by
  cases strt with
  | DefStructT st => exact strtype_struct_success_iff_valid c st start finalSupply
  | DefArrayT arrayTy => exact strtype_array_success_iff_valid c arrayTy start finalSupply
  | DefFuncT ft => exact strtype_func_success_iff_valid c ft start finalSupply

end properties.wasm_module_not_ok.Rejection
