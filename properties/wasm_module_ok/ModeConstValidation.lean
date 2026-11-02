import properties.wasm_module_ok.ElemDataConstValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ModeConstValidation

theorem datamode_active_const
    (c : SpecTec.context) (a : SpecTec.active)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Datamode_ok c (.Active a)⟩)
      n (.success (.of ())) finalSupply) :
    ∃ (vt : SpecTec.valtype) (start finish : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Const_ok c vt a.OFFSET⟩)
        start (.success (.of ())) finish := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (.orElse (SpecTec.«Datamode_ok:clause:0» c (.Active a))
        (fun _ => SpecTecExecution.tryClauses
          [fun _ => SpecTec.«Datamode_ok:clause:1» c (.Active a)]))
      n (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«Datamode_ok:clause:0» at hfirst
      cases hfirst with
      | bind_success hguard _ =>
        cases hguard with
        | guard_true hfalse =>
          simp [SpecTec.«exec:match:datamode:Passive»] at hfalse
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Datamode_ok:clause:1» c (.Active a))
          (fun _ => .unmatch))
        n (.success (.of ())) finalSupply at htail
      cases htail with
      | orElse_success hactive =>
        unfold SpecTec.«Datamode_ok:clause:1» at hactive
        cases hactive with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true _ =>
            cases htail with
            | bind_success hbound htail =>
              cases hbound with
              | guard_true _ =>
                cases hlookup : c.MEMS[a.INDEX]? with
                | none => simp only [hlookup] at htail; cases htail
                | some mt =>
                  simp only [hlookup] at htail
                  cases mt with
                  | MemoryT addr lim =>
                    cases htail with
                    | bind_success hnum htail =>
                      cases htail with
                      | bind_success hconst _ =>
                        exact ⟨_, _, _, hconst⟩
      | orElse_unmatch _ hnone => cases hnone

theorem elemmode_active_const
    (c : SpecTec.context) (rt : SpecTec.reftype)
    (a : SpecTec.active) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Elemmode_ok c rt (.Active a)⟩)
      n (.success (.of ())) finalSupply) :
    ∃ (vt : SpecTec.valtype) (start finish : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Const_ok c vt a.OFFSET⟩)
        start (.success (.of ())) finish := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (.orElse (SpecTec.«Elemmode_ok:clause:0» c rt (.Active a))
        (fun _ => SpecTecExecution.tryClauses
          [fun _ => SpecTec.«Elemmode_ok:clause:1» c rt (.Active a),
           fun _ => SpecTec.«Elemmode_ok:clause:2» c rt (.Active a)]))
      n (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«Elemmode_ok:clause:0» at hfirst
      cases hfirst with
      | bind_success hguard _ =>
        cases hguard with
        | guard_true hfalse =>
          simp [SpecTec.«exec:match:elemmode:Passive»] at hfalse
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Elemmode_ok:clause:1» c rt (.Active a))
          (fun _ => SpecTecExecution.tryClauses
            [fun _ => SpecTec.«Elemmode_ok:clause:2» c rt (.Active a)]))
        n (.success (.of ())) finalSupply at htail
      cases htail with
      | orElse_success hactive =>
        unfold SpecTec.«Elemmode_ok:clause:1» at hactive
        cases hactive with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true _ =>
            cases htail with
            | bind_success hbound htail =>
              cases hbound with
              | guard_true _ =>
                cases hlookup : c.TABLES[a.INDEX]? with
                | none => simp only [hlookup] at htail; cases htail
                | some tt =>
                  simp only [hlookup] at htail
                  cases tt with
                  | TableT addr lim rt' =>
                    cases htail with
                    | bind_success hmatch htail =>
                      cases htail with
                      | bind_success hmatchguard htail =>
                        cases hmatchguard with
                        | guard_true _ =>
                          cases htail with
                          | bind_success hnum htail =>
                            cases htail with
                            | bind_success hconst _ =>
                              exact ⟨_, _, _, hconst⟩
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Elemmode_ok:clause:2» c rt (.Active a))
            (fun _ => .unmatch))
          n (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hthird =>
          unfold SpecTec.«Elemmode_ok:clause:2» at hthird
          cases hthird with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hfalse =>
              simp [SpecTec.«exec:match:elemmode:Declarative»] at hfalse
        | orElse_unmatch _ hnone => cases hnone

end properties.wasm_module_ok.ModeConstValidation
