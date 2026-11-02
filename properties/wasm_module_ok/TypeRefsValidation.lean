import properties.wasm_module_ok.ContextRefsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.TypeRefsValidation

theorem rectype_ok_refs (c result : SpecTec.context)
    (rt : SpecTec.rectype) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Rectype_ok c rt⟩)
      n (.success (.of result)) finalSupply) :
    result.REFS = c.REFS := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Rectype_ok_clauses c rt))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      cases rt with
      | RecT sts =>
        unfold SpecTec.«Rectype_ok:clause:0» at hclause
        cases hclause with
        | bind_success _ htail =>
          cases htail with
          | bind_success _ htail =>
            cases htail with
            | bind_success _ htail =>
              cases htail with
              | bind_success _ htail =>
                cases htail with
                | bind_success _ htail =>
                  cases htail with
                  | bind_success _ hpure =>
                    cases hpure with
                    | pure => rfl
    | orElse_unmatch _ hnone => cases hnone

theorem type_ok_refs (c result : SpecTec.context)
    (t : SpecTec.type) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Type_ok c t⟩)
      n (.success (.of result)) finalSupply) :
    result.REFS = c.REFS := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Type_ok_clauses c t))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«Type_ok:clause:0» at hclause
      cases hclause with
      | bind_success hrect hpure =>
        cases hpure with
        | pure => exact rectype_ok_refs c result t n finalSupply hrect
    | orElse_unmatch _ hnone => cases hnone

theorem types_ok_refs (c result : SpecTec.context)
    (ts : List SpecTec.type) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Types_ok c ts⟩)
      n (.success (.of result)) finalSupply) :
    result.REFS = c.REFS := by
  induction ts generalizing c n finalSupply result with
  | nil =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Types_ok:clause:0» c [])
            (fun _ => SpecTecExecution.tryClauses
              [fun _ => SpecTec.«Types_ok:clause:1» c []]))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Types_ok:clause:0» at hfirst
          cases hfirst with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond => simp at hcond
        | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Types_ok:clause:1» c [])
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Types_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success _ hpure =>
              cases hpure with
              | pure => rfl
          | orElse_unmatch _ hnone => cases hnone
  | cons t rest ih =>
      cases hcall with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Types_ok:clause:0» c (t :: rest))
            (fun _ => SpecTecExecution.tryClauses
              [fun _ => SpecTec.«Types_ok:clause:1» c (t :: rest)]))
          n (.success (.of result)) finalSupply at hbody
        cases hbody with
        | orElse_success hfirst =>
          unfold SpecTec.«Types_ok:clause:0» at hfirst
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
                      (type_ok_refs c c₁ t n middle hhead)
        | orElse_unmatch _ htail =>
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Types_ok:clause:1» c (t :: rest))
              (fun _ => .unmatch))
            n (.success (.of result)) finalSupply at htail
          cases htail with
          | orElse_success hsecond =>
            unfold SpecTec.«Types_ok:clause:1» at hsecond
            cases hsecond with
            | bind_success hguard _ =>
              cases hguard with
              | guard_true hcond => simp at hcond
          | orElse_unmatch _ hnone => cases hnone

end properties.wasm_module_ok.TypeRefsValidation
