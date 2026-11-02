import properties.wasm_module_ok.ElemDataCallValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ElemDataConstValidation

theorem elem_ok_initializer_and_mode
    (c result : SpecTec.context) (e : SpecTec.elem)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Elem_ok c e⟩)
      n (.success (.of result)) finalSupply) :
    (∃ start finish : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.«Elem_ok:rule:iter:0»
          c e.ETYPE e.EINIT⟩)
        start (.success (.of ())) finish) ∧
    (∃ start finish : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Elemmode_ok
          c e.ETYPE e.EMODE⟩)
        start (.success (.of ())) finish) := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Elem_ok_clauses c e))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«Elem_ok:clause:0» at hclause
      cases hclause with
      | bind_success _ htail =>
        cases htail with
        | bind_success hiter htail =>
          cases htail with
          | bind_success hmode _ =>
            exact ⟨⟨_, _, hiter⟩, ⟨_, _, hmode⟩⟩
    | orElse_unmatch _ hnone => cases hnone

theorem data_ok_mode
    (c result : SpecTec.context) (d : SpecTec.data)
    (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Data_ok c d⟩)
      n (.success (.of result)) finalSupply) :
    ∃ start finish : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Datamode_ok c d.DMODE⟩)
        start (.success (.of ())) finish := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Data_ok_clauses c d))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«Data_ok:clause:0» at hclause
      cases hclause with
      | bind_success hmode _ => exact ⟨_, _, hmode⟩
    | orElse_unmatch _ hnone => cases hnone

theorem elem_iter_cons_success_iff
    (c : SpecTec.context) (rt : SpecTec.reftype)
    (init : SpecTec.const) (rest : List SpecTec.const)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Elem_ok:rule:iter:0»
        c rt (init :: rest)⟩)
      n (.success (.of ())) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Const_ok c (.RefT rt) init⟩)
        n (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.«Elem_ok:rule:iter:0» c rt rest⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Elem_ok:rule:iter:0:clause:0» c rt (init :: rest))
          (fun _ => SpecTecExecution.tryClauses
            [fun _ => SpecTec.«Elem_ok:rule:iter:0:clause:1»
              c rt (init :: rest)]))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Elem_ok:rule:iter:0:clause:0» at hfirst
        cases hfirst
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Elem_ok:rule:iter:0:clause:1» c rt (init :: rest))
            (fun _ => .unmatch))
          n (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Elem_ok:rule:iter:0:clause:1» at hsecond
          cases hsecond with
          | bind_success hconst htail =>
            cases htail with
            | bind_success hrest hpure =>
              cases hpure with
              | pure => exact ⟨_, hconst, hrest⟩
        | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨middle, hconst, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«Elem_ok:rule:iter:0_clauses» c rt (init :: rest)))
      n (.success (.of ())) finalSupply
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Elem_ok:rule:iter:0:clause:0» c rt (init :: rest))
        n .unmatch n
      unfold SpecTec.«Elem_ok:rule:iter:0:clause:0»
      exact SpecTecExecution.Eval.unmatch
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Elem_ok:rule:iter:0:clause:1» c rt (init :: rest))
      n (.success (.of ())) finalSupply
    unfold SpecTec.«Elem_ok:rule:iter:0:clause:1»
    apply SpecTecExecution.Eval.bind_success hconst
    apply SpecTecExecution.Eval.bind_success hrest
    exact SpecTecExecution.Eval.pure _

theorem elem_iter_member_const
    (c : SpecTec.context) (rt : SpecTec.reftype)
    (inits : List SpecTec.const) (n finalSupply : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.«Elem_ok:rule:iter:0» c rt inits⟩)
      n (.success (.of ())) finalSupply)
    (init : SpecTec.const) (hmem : init ∈ inits) :
    ∃ start finish : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Const_ok c (.RefT rt) init⟩)
        start (.success (.of ())) finish := by
  induction inits generalizing n finalSupply with
  | nil => simp at hmem
  | cons head rest ih =>
      obtain ⟨middle, hhead, htail⟩ :=
        (elem_iter_cons_success_iff c rt head rest n finalSupply).mp hcall
      rcases List.mem_cons.mp hmem with heq | hrestmem
      · subst heq
        exact ⟨n, middle, hhead⟩
      · exact ih middle finalSupply htail hrestmem

end properties.wasm_module_ok.ElemDataConstValidation
