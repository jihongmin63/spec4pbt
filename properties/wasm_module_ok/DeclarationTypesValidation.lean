import properties.wasm_module_ok.DeclarationRefsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.DeclarationTypesValidation

theorem table_ok_types (c result : SpecTec.context)
    (t : SpecTec.table) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Table_ok c t⟩)
      n (.success (.of result)) finalSupply) :
    result.TYPES = c.TYPES := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Table_ok_clauses c t) ())
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«Table_ok:clause:0» at hclause
      cases hclause with
      | bind_success _ htail =>
        cases htail with
        | bind_success _ hpure =>
          cases hpure with
          | pure => rfl
    | orElse_unmatch _ hnone => cases hnone

theorem global_ok_types (c result : SpecTec.context)
    (g : SpecTec.global) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Global_ok c g⟩)
      n (.success (.of result)) finalSupply) :
    result.TYPES = c.TYPES := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Global_ok_clauses c g) ())
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«Global_ok:clause:0» at hclause
      cases hclause with
      | bind_success _ htail =>
        cases htail with
        | bind_success _ hpure =>
          cases hpure with
          | pure => rfl
    | orElse_unmatch _ hnone => cases hnone

theorem elem_ok_types (c result : SpecTec.context)
    (e : SpecTec.elem) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Elem_ok c e⟩)
      n (.success (.of result)) finalSupply) :
    result.TYPES = c.TYPES := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Elem_ok_clauses c e) ())
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«Elem_ok:clause:0» at hclause
      cases hclause with
      | bind_success _ htail =>
        cases htail with
        | bind_success _ htail =>
          cases htail with
          | bind_success _ hpure =>
            cases hpure with
            | pure => rfl
    | orElse_unmatch _ hnone => cases hnone

theorem data_ok_types (c result : SpecTec.context)
    (d : SpecTec.data) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Data_ok c d⟩)
      n (.success (.of result)) finalSupply) :
    result.TYPES = c.TYPES := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Data_ok_clauses c d) ())
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«Data_ok:clause:0» at hclause
      cases hclause with
      | bind_success _ hpure =>
        cases hpure with
        | pure => rfl
    | orElse_unmatch _ hnone => cases hnone

theorem tables_ok_types (c result : SpecTec.context)
    (ts : List SpecTec.table) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Tables_ok c ts⟩)
      n (.success (.of result)) finalSupply) :
    result.TYPES = c.TYPES := by
  induction ts generalizing c n finalSupply result with
  | nil =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Tables_ok:clause:0» c [])
            (fun _ => SpecTecExecution.firstSuccess
              [fun _ => SpecTec.«Tables_ok:clause:1» c []] ()))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Tables_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Tables_ok:clause:1» c [])
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Tables_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success _ hpure =>
              cases hpure with
              | pure => rfl
          | orElse_unmatch _ hnone => cases hnone
  | cons t rest ih =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Tables_ok:clause:0» c (t :: rest))
            (fun _ => SpecTecExecution.firstSuccess
              [fun _ => SpecTec.«Tables_ok:clause:1» c (t :: rest)] ()))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Tables_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard htail =>
            cases hguard with
            | guard_true _ =>
              cases htail with
              | bind_success hhead htail =>
                rename_i middle c₁
                cases htail with
                | bind_success hrest hpure =>
                  cases hpure with
                  | pure =>
                    exact (ih c₁ result middle finalSupply hrest).trans
                      (table_ok_types c c₁ t n middle hhead)
        | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Tables_ok:clause:1» c (t :: rest))
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Tables_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond => simp at hcond
          | orElse_unmatch _ hnone => cases hnone

theorem globals_ok_types (c result : SpecTec.context)
    (ts : List SpecTec.global) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Globals_ok c ts⟩)
      n (.success (.of result)) finalSupply) :
    result.TYPES = c.TYPES := by
  induction ts generalizing c n finalSupply result with
  | nil =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Globals_ok:clause:0» c [])
            (fun _ => SpecTecExecution.firstSuccess
              [fun _ => SpecTec.«Globals_ok:clause:1» c []] ()))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Globals_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Globals_ok:clause:1» c [])
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Globals_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success _ hpure =>
              cases hpure with
              | pure => rfl
          | orElse_unmatch _ hnone => cases hnone
  | cons t rest ih =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Globals_ok:clause:0» c (t :: rest))
            (fun _ => SpecTecExecution.firstSuccess
              [fun _ => SpecTec.«Globals_ok:clause:1» c (t :: rest)] ()))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Globals_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard htail =>
            cases hguard with
            | guard_true _ =>
              cases htail with
              | bind_success hhead htail =>
                rename_i middle c₁
                cases htail with
                | bind_success hrest hpure =>
                  cases hpure with
                  | pure =>
                    exact (ih c₁ result middle finalSupply hrest).trans
                      (global_ok_types c c₁ t n middle hhead)
        | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Globals_ok:clause:1» c (t :: rest))
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Globals_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond => simp at hcond
          | orElse_unmatch _ hnone => cases hnone

theorem elems_ok_types (c result : SpecTec.context)
    (ts : List SpecTec.elem) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Elems_ok c ts⟩)
      n (.success (.of result)) finalSupply) :
    result.TYPES = c.TYPES := by
  induction ts generalizing c n finalSupply result with
  | nil =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Elems_ok:clause:0» c [])
            (fun _ => SpecTecExecution.firstSuccess
              [fun _ => SpecTec.«Elems_ok:clause:1» c []] ()))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Elems_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Elems_ok:clause:1» c [])
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Elems_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success _ hpure =>
              cases hpure with
              | pure => rfl
          | orElse_unmatch _ hnone => cases hnone
  | cons t rest ih =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Elems_ok:clause:0» c (t :: rest))
            (fun _ => SpecTecExecution.firstSuccess
              [fun _ => SpecTec.«Elems_ok:clause:1» c (t :: rest)] ()))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Elems_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard htail =>
            cases hguard with
            | guard_true _ =>
              cases htail with
              | bind_success hhead htail =>
                rename_i middle c₁
                cases htail with
                | bind_success hrest hpure =>
                  cases hpure with
                  | pure =>
                    exact (ih c₁ result middle finalSupply hrest).trans
                      (elem_ok_types c c₁ t n middle hhead)
        | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Elems_ok:clause:1» c (t :: rest))
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Elems_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond => simp at hcond
          | orElse_unmatch _ hnone => cases hnone

theorem datas_ok_types (c result : SpecTec.context)
    (ts : List SpecTec.data) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Datas_ok c ts⟩)
      n (.success (.of result)) finalSupply) :
    result.TYPES = c.TYPES := by
  induction ts generalizing c n finalSupply result with
  | nil =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Datas_ok:clause:0» c [])
            (fun _ => SpecTecExecution.firstSuccess
              [fun _ => SpecTec.«Datas_ok:clause:1» c []] ()))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Datas_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Datas_ok:clause:1» c [])
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Datas_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success _ hpure =>
              cases hpure with
              | pure => rfl
          | orElse_unmatch _ hnone => cases hnone
  | cons t rest ih =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Datas_ok:clause:0» c (t :: rest))
            (fun _ => SpecTecExecution.firstSuccess
              [fun _ => SpecTec.«Datas_ok:clause:1» c (t :: rest)] ()))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Datas_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard htail =>
            cases hguard with
            | guard_true _ =>
              cases htail with
              | bind_success hhead htail =>
                rename_i middle c₁
                cases htail with
                | bind_success hrest hpure =>
                  cases hpure with
                  | pure =>
                    exact (ih c₁ result middle finalSupply hrest).trans
                      (data_ok_types c c₁ t n middle hhead)
        | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Datas_ok:clause:1» c (t :: rest))
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Datas_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond => simp at hcond
          | orElse_unmatch _ hnone => cases hnone

end properties.wasm_module_ok.DeclarationTypesValidation
