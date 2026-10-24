import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.StartValidation

theorem start_none_success (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Start_ok c none⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Start_ok_clauses c none) ())
    n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Start_ok:clause:0» c none) n .unmatch n
    unfold SpecTec.«Start_ok:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    simp
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Start_ok:clause:1» c none)
      n (.success (.of ())) n
    unfold SpecTec.«Start_ok:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      simp
    · exact SpecTecExecution.Eval.pure ()

theorem functype_of_strtype_success_iff
    (st : SpecTec.strtype) (ft : SpecTec.functype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.functype,
        SpecTec.SpecTecCall.«$functype_of_strtype» st⟩)
      n (.success (.of ft)) finalSupply ↔
      st = .DefFuncT ft ∧ finalSupply = n := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$functype_of_strtype_clauses» st) ())
        n (.success (.of ft)) finalSupply at hbody
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«$functype_of_strtype:clause:0» st)
          (fun _ => .unmatch))
        n (.success (.of ft)) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«$functype_of_strtype:clause:0» at hclause
        cases hclause with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true hcond =>
            cases st with
            | DefStructT _ => simp [SpecTec.«exec:match:strtype:DefFuncT»] at hcond
            | DefArrayT _ => simp [SpecTec.«exec:match:strtype:DefFuncT»] at hcond
            | DefFuncT ft' =>
              cases htail with
              | pure => exact ⟨rfl, rfl⟩
      | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨hshape, hsupply⟩
    subst st
    subst finalSupply
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$functype_of_strtype_clauses» (.DefFuncT ft)) ())
      n (.success (.of ft)) n
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$functype_of_strtype:clause:0» (.DefFuncT ft))
      n (.success (.of ft)) n
    unfold SpecTec.«$functype_of_strtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      rfl
    · exact SpecTecExecution.Eval.pure ft

theorem start_some_of_expanddt
    (c : SpecTec.context) (s : SpecTec.start) (dt : SpecTec.deftype)
    (n finalSupply : Nat)
    (hget : c.FUNCS[s.SFUNC]? = some dt)
    (hexpand : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of (SpecTec.strtype.DefFuncT
        (SpecTec.functype.FuncT [] [])))) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Start_ok c (some s)⟩)
      n (.success (.of ())) finalSupply := by
  have hindex : s.SFUNC < c.FUNCS.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Start_ok_clauses c (some s)) ())
    n (.success (.of ())) finalSupply
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Start_ok:clause:0» c (some s))
    n (.success (.of ())) finalSupply
  unfold SpecTec.«Start_ok:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · apply SpecTecExecution.Eval.guard_true
    rfl
  · apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      exact hindex
    · rw [hget]
      apply SpecTecExecution.Eval.bind_success hexpand
      apply SpecTecExecution.Eval.bind_success
        ((functype_of_strtype_success_iff
          (.DefFuncT (.FuncT [] [])) (.FuncT [] [])
          finalSupply finalSupply).2 ⟨rfl, rfl⟩)
      exact SpecTecExecution.Eval.pure ()

theorem start_some_success_inv
    (c : SpecTec.context) (s : SpecTec.start)
    (n finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Start_ok c (some s)⟩)
      n (.success (.of ())) finalSupply) :
    ∃ dt : SpecTec.deftype,
      c.FUNCS[s.SFUNC]? = some dt ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
        n (.success (.of (SpecTec.strtype.DefFuncT
          (SpecTec.functype.FuncT [] [])))) finalSupply := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Start_ok_clauses c (some s)) ())
      n (.success (.of ())) finalSupply at hbody
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (.orElse (SpecTec.«Start_ok:clause:0» c (some s))
        (fun _ => SpecTecExecution.firstSuccess
          [fun _ => SpecTec.«Start_ok:clause:1» c (some s)] ()))
      n (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«Start_ok:clause:0» at hfirst
      cases hfirst with
      | bind_success hsome htail =>
        cases hsome with
        | guard_true _ =>
          cases htail with
          | bind_success hbound htail =>
            cases hbound with
            | guard_true _ =>
              cases hget : c.FUNCS[s.SFUNC]? with
              | none =>
                rw [hget] at htail
                cases htail
              | some dt =>
                rw [hget] at htail
                cases htail with
                | bind_success hexpand htail =>
                  cases htail with
                  | bind_success hfun htail =>
                    obtain ⟨hshape, hsupply⟩ :=
                      (functype_of_strtype_success_iff _ _ _ _).1 hfun
                    cases hshape
                    cases hsupply
                    rename_i params
                    cases params with
                    | FuncT args results =>
                      cases args with
                      | nil =>
                        cases results with
                        | nil =>
                          cases htail with
                          | pure => exact ⟨dt, rfl, hexpand⟩
                        | cons _ _ => cases htail
                      | cons _ _ => cases htail
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Start_ok:clause:1» c (some s))
          (fun _ => .unmatch))
        n (.success (.of ())) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Start_ok:clause:1» at hsecond
        cases hsecond with
        | bind_success hnone _ =>
          cases hnone with
          | guard_true hcond => simp at hcond
      | orElse_unmatch _ hlast => cases hlast

theorem start_some_success_iff
    (c : SpecTec.context) (s : SpecTec.start)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Start_ok c (some s)⟩)
      n (.success (.of ())) finalSupply ↔
    ∃ dt : SpecTec.deftype,
      c.FUNCS[s.SFUNC]? = some dt ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
        n (.success (.of (SpecTec.strtype.DefFuncT
          (SpecTec.functype.FuncT [] [])))) finalSupply := by
  constructor
  · exact start_some_success_inv c s n finalSupply
  · rintro ⟨dt, hget, hexpand⟩
    exact start_some_of_expanddt c s dt n finalSupply hget hexpand

theorem expanddt_success_iff_unrolldt
    (dt : SpecTec.deftype) (st : SpecTec.strtype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.strtype, SpecTec.SpecTecCall.«$expanddt» dt⟩)
      n (.success (.of st)) finalSupply ↔
    ∃ (fin : SpecTec.final) (supers : List SpecTec.heaptype),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dt⟩)
        n (.success (.of (SpecTec.subtype.SubT fin supers st))) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$expanddt_clauses» dt) ())
        n (.success (.of st)) finalSupply at hbody
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«$expanddt:clause:0» dt)
          (fun _ => .unmatch))
        n (.success (.of st)) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«$expanddt:clause:0» at hclause
        cases hclause with
        | bind_success hunroll htail =>
          rename_i middle subtypeValue
          cases subtypeValue with
          | SubT fin supers strt =>
            cases htail with
            | pure => exact ⟨fin, supers, hunroll⟩
      | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨fin, supers, hunroll⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$expanddt_clauses» dt) ())
      n (.success (.of st)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$expanddt:clause:0» dt)
      n (.success (.of st)) finalSupply
    unfold SpecTec.«$expanddt:clause:0»
    apply SpecTecExecution.Eval.bind_success hunroll
    exact SpecTecExecution.Eval.pure st

theorem start_some_success_iff_unrolldt
    (c : SpecTec.context) (s : SpecTec.start)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Start_ok c (some s)⟩)
      n (.success (.of ())) finalSupply ↔
    ∃ (dt : SpecTec.deftype) (fin : SpecTec.final)
        (supers : List SpecTec.heaptype),
      c.FUNCS[s.SFUNC]? = some dt ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.subtype, SpecTec.SpecTecCall.«$unrolldt» dt⟩)
        n (.success (.of (SpecTec.subtype.SubT fin supers
          (.DefFuncT (.FuncT [] []))))) finalSupply := by
  rw [start_some_success_iff]
  constructor
  · rintro ⟨dt, hget, hexpand⟩
    obtain ⟨fin, supers, hunroll⟩ :=
      (expanddt_success_iff_unrolldt dt
        (.DefFuncT (.FuncT [] [])) n finalSupply).1 hexpand
    exact ⟨dt, fin, supers, hget, hunroll⟩
  · rintro ⟨dt, fin, supers, hget, hunroll⟩
    exact ⟨dt, hget,
      (expanddt_success_iff_unrolldt dt
        (.DefFuncT (.FuncT [] [])) n finalSupply).2
        ⟨fin, supers, hunroll⟩⟩

end properties.wasm_module_ok.StartValidation
