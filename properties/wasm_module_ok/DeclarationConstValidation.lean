import properties.wasm_module_ok.ConstNestedValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.DeclarationConstValidation

theorem table_ok_initializer_const
    (c result : SpecTec.context) (t : SpecTec.table)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Table_ok c t⟩)
      n (.success (.of result)) finalSupply) :
    ∃ (vt : SpecTec.valtype) (start finish : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Const_ok c vt t.TINIT⟩)
        start (.success (.of ())) finish := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Table_ok_clauses c t))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      cases htype : t.TTYPE with
      | TableT addr lim rt =>
        unfold SpecTec.«Table_ok:clause:0» at hclause
        rw [htype] at hclause
        cases hclause with
        | bind_success _ htail =>
          cases htail with
          | bind_success hconst _ => exact ⟨.RefT rt, _, _, hconst⟩
    | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem global_ok_initializer_const
    (c result : SpecTec.context) (g : SpecTec.global)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Global_ok c g⟩)
      n (.success (.of result)) finalSupply) :
    ∃ (vt : SpecTec.valtype) (start finish : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Const_ok c vt g.GINIT⟩)
        start (.success (.of ())) finish := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Global_ok_clauses c g))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      cases htype : g.GTYPE with
      | GlobalT mutability vt =>
        unfold SpecTec.«Global_ok:clause:0» at hclause
        rw [htype] at hclause
        cases hclause with
        | bind_success _ htail =>
          cases htail with
          | bind_success hconst _ => exact ⟨vt, _, _, hconst⟩
    | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem tables_ok_member_const
    (c result : SpecTec.context) (ts : List SpecTec.table)
    (t : SpecTec.table) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Tables_ok c ts⟩)
      n (.success (.of result)) finalSupply)
    (hmem : t ∈ ts) :
    ∃ (localContext : SpecTec.context) (vt : SpecTec.valtype)
      (start finish : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Const_ok
          localContext vt t.TINIT⟩)
        start (.success (.of ())) finish := by
  induction ts generalizing c result n finalSupply with
  | nil => simp at hmem
  | cons head rest ih =>
    cases hcall with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Tables_ok:clause:0» c (head :: rest))
          (fun _ => SpecTecExecution.tryClauses
            [SpecTec.«Tables_ok:clause:1» c (head :: rest)]))
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
              | bind_success hrest _ =>
                rcases List.mem_cons.mp hmem with heq | hrestmem
                · subst heq
                  obtain ⟨vt, start, finish, hconst⟩ :=
                    table_ok_initializer_const c c₁ t n middle hhead
                  exact ⟨c, vt, start, finish, hconst⟩
                · exact ih c₁ _ middle _ hrest hrestmem
      | orElse_unmatch hfailedSupply htail =>
        restore_supply hfailedSupply at htail
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Tables_ok:clause:1» c (head :: rest))
            (fun _ => .unmatch))
          n (.success (.of result)) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Tables_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem globals_ok_member_const
    (c result : SpecTec.context) (gs : List SpecTec.global)
    (g : SpecTec.global) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Globals_ok c gs⟩)
      n (.success (.of result)) finalSupply)
    (hmem : g ∈ gs) :
    ∃ (localContext : SpecTec.context) (vt : SpecTec.valtype)
      (start finish : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Const_ok
          localContext vt g.GINIT⟩)
        start (.success (.of ())) finish := by
  induction gs generalizing c result n finalSupply with
  | nil => simp at hmem
  | cons head rest ih =>
    cases hcall with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Globals_ok:clause:0» c (head :: rest))
          (fun _ => SpecTecExecution.tryClauses
            [SpecTec.«Globals_ok:clause:1» c (head :: rest)]))
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
              | bind_success hrest _ =>
                rcases List.mem_cons.mp hmem with heq | hrestmem
                · subst heq
                  obtain ⟨vt, start, finish, hconst⟩ :=
                    global_ok_initializer_const c c₁ g n middle hhead
                  exact ⟨c, vt, start, finish, hconst⟩
                · exact ih c₁ _ middle _ hrest hrestmem
      | orElse_unmatch hfailedSupply htail =>
        restore_supply hfailedSupply at htail
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Globals_ok:clause:1» c (head :: rest))
            (fun _ => .unmatch))
          n (.success (.of result)) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Globals_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

end properties.wasm_module_ok.DeclarationConstValidation
