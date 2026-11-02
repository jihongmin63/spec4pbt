import properties.wasm_module_ok.RefCycleTrace

set_option autoImplicit false

namespace properties.wasm_module_ok.ElemDataCallValidation

theorem elems_ok_member_call
    (c result : SpecTec.context) (es : List SpecTec.elem)
    (e : SpecTec.elem) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Elems_ok c es⟩)
      n (.success (.of result)) finalSupply)
    (hmem : e ∈ es) :
    ∃ (localContext produced : SpecTec.context) (start finish : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Elem_ok
          localContext e⟩)
        start (.success (.of produced)) finish := by
  induction es generalizing c result n finalSupply with
  | nil => simp at hmem
  | cons head rest ih =>
    cases hcall with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Elems_ok:clause:0» c (head :: rest))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«Elems_ok:clause:1» c (head :: rest)] ()))
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
              | bind_success hrest _ =>
                rcases List.mem_cons.mp hmem with heq | hrestmem
                · subst heq
                  exact ⟨c, c₁, n, middle, hhead⟩
                · exact ih c₁ _ middle _ hrest hrestmem
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Elems_ok:clause:1» c (head :: rest))
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

theorem datas_ok_member_call
    (c result : SpecTec.context) (ds : List SpecTec.data)
    (d : SpecTec.data) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Datas_ok c ds⟩)
      n (.success (.of result)) finalSupply)
    (hmem : d ∈ ds) :
    ∃ (localContext produced : SpecTec.context) (start finish : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Data_ok
          localContext d⟩)
        start (.success (.of produced)) finish := by
  induction ds generalizing c result n finalSupply with
  | nil => simp at hmem
  | cons head rest ih =>
    cases hcall with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Datas_ok:clause:0» c (head :: rest))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«Datas_ok:clause:1» c (head :: rest)] ()))
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
              | bind_success hrest _ =>
                rcases List.mem_cons.mp hmem with heq | hrestmem
                · subst heq
                  exact ⟨c, c₁, n, middle, hhead⟩
                · exact ih c₁ _ middle _ hrest hrestmem
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«Datas_ok:clause:1» c (head :: rest))
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

end properties.wasm_module_ok.ElemDataCallValidation
