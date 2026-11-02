import properties.wasm_module_not_ok.SubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem rectype_iter5_nil_success (c : SpecTec.context) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c []⟩)
      start (.success (.of ())) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Rectype_ok:rule:iter:5_clauses» c []) ())
    start (.success (.of ())) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Rectype_ok:rule:iter:5:clause:0» c [])
    start (.success (.of ())) start
  exact SpecTecExecution.Eval.pure ()

theorem rectype_iter5_cons_success (c : SpecTec.context)
    (st : SpecTec.subtype) (sts : List SpecTec.subtype)
    (start middle finalSupply : Nat)
    (hhead : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_ok c st⟩)
      start (.success (.of ())) middle)
    (htail : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c sts⟩)
      middle (.success (.of ())) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Rectype_ok:rule:iter:5_clauses» c (st :: sts)) ())
    start (.success (.of ())) finalSupply
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Rectype_ok:rule:iter:5:clause:0» c (st :: sts))
      start .unmatch start
    exact SpecTecExecution.Eval.unmatch
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Rectype_ok:rule:iter:5:clause:1» c (st :: sts))
      start (.success (.of ())) finalSupply
    unfold SpecTec.«Rectype_ok:rule:iter:5:clause:1»
    apply SpecTecExecution.Eval.bind_success hhead
    apply SpecTecExecution.Eval.bind_success htail
    exact SpecTecExecution.Eval.pure ()

theorem rectype_iter5_cons_success_inv (c : SpecTec.context)
    (st : SpecTec.subtype) (sts : List SpecTec.subtype)
    (start finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply) :
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_ok c st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c sts⟩)
        middle (.success (.of ())) finalSupply := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Rectype_ok:rule:iter:5_clauses» c (st :: sts)) ())
      start (.success (.of ())) finalSupply at hbody
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (.orElse (SpecTec.«Rectype_ok:rule:iter:5:clause:0» c (st :: sts))
        (fun _ => SpecTecExecution.firstSuccess
          [fun _ => SpecTec.«Rectype_ok:rule:iter:5:clause:1» c (st :: sts)] ()))
      start (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      change SpecTecExecution.Eval SpecTec.specTecProgram .unmatch
        start (.success (.of ())) finalSupply at hfirst
      cases hfirst
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Rectype_ok:rule:iter:5:clause:1» c (st :: sts))
          (fun _ => .unmatch))
        start (.success (.of ())) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Rectype_ok:rule:iter:5:clause:1» at hsecond
        cases hsecond with
        | bind_success hhead hrest =>
          cases hrest with
          | bind_success htail hpure =>
            cases hpure with
            | pure => exact ⟨_, hhead, htail⟩
      | orElse_unmatch _ hlast => cases hlast

theorem rectype_iter5_cons_success_iff (c : SpecTec.context)
    (st : SpecTec.subtype) (sts : List SpecTec.subtype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_ok c st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Rectype_ok:rule:iter:5» c sts⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · exact rectype_iter5_cons_success_inv c st sts start finalSupply
  · rintro ⟨middle, hhead, htail⟩
    exact rectype_iter5_cons_success c st sts start middle finalSupply hhead htail

theorem rectype_iter6_nil_success (c : SpecTec.context)
    (x start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6» c x [] []⟩)
      start (.success (.of ())) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Rectype_ok:rule:iter:6_clauses» c x [] []) ())
    start (.success (.of ())) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Rectype_ok:rule:iter:6:clause:0» c x [] [])
    start (.success (.of ())) start
  exact SpecTecExecution.Eval.pure ()

theorem rectype_iter6_cons_success (c : SpecTec.context)
    (x n : Nat) (ns : List Nat)
    (st : SpecTec.subtype) (sts : List SpecTec.subtype)
    (start middle finalSupply : Nat)
    (hhead : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_sub_ok c (x + n) st⟩)
      start (.success (.of ())) middle)
    (htail : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6» c x ns sts⟩)
      middle (.success (.of ())) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6» c x
          (n :: ns) (st :: sts)⟩)
      start (.success (.of ())) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Rectype_ok:rule:iter:6_clauses» c x (n :: ns) (st :: sts)) ())
    start (.success (.of ())) finalSupply
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Rectype_ok:rule:iter:6:clause:0» c x (n :: ns) (st :: sts))
      start .unmatch start
    exact SpecTecExecution.Eval.unmatch
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Rectype_ok:rule:iter:6:clause:1» c x (n :: ns) (st :: sts))
      start (.success (.of ())) finalSupply
    unfold SpecTec.«Rectype_ok:rule:iter:6:clause:1»
    apply SpecTecExecution.Eval.bind_success hhead
    apply SpecTecExecution.Eval.bind_success htail
    exact SpecTecExecution.Eval.pure ()

theorem rectype_iter6_cons_success_inv (c : SpecTec.context)
    (x n : Nat) (ns : List Nat)
    (st : SpecTec.subtype) (sts : List SpecTec.subtype)
    (start finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6» c x
          (n :: ns) (st :: sts)⟩)
      start (.success (.of ())) finalSupply) :
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_sub_ok c (x + n) st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6» c x ns sts⟩)
        middle (.success (.of ())) finalSupply := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Rectype_ok:rule:iter:6_clauses» c x (n :: ns) (st :: sts)) ())
      start (.success (.of ())) finalSupply at hbody
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (.orElse
        (SpecTec.«Rectype_ok:rule:iter:6:clause:0» c x (n :: ns) (st :: sts))
        (fun _ => SpecTecExecution.firstSuccess
          [fun _ => SpecTec.«Rectype_ok:rule:iter:6:clause:1»
            c x (n :: ns) (st :: sts)] ()))
      start (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      change SpecTecExecution.Eval SpecTec.specTecProgram .unmatch
        start (.success (.of ())) finalSupply at hfirst
      cases hfirst
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse
          (SpecTec.«Rectype_ok:rule:iter:6:clause:1» c x (n :: ns) (st :: sts))
          (fun _ => .unmatch))
        start (.success (.of ())) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Rectype_ok:rule:iter:6:clause:1» at hsecond
        cases hsecond with
        | bind_success hhead hrest =>
          cases hrest with
          | bind_success htail hpure =>
            cases hpure with
            | pure => exact ⟨_, hhead, htail⟩
      | orElse_unmatch _ hlast => cases hlast

theorem rectype_iter6_cons_success_iff (c : SpecTec.context)
    (x n : Nat) (ns : List Nat)
    (st : SpecTec.subtype) (sts : List SpecTec.subtype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6» c x
          (n :: ns) (st :: sts)⟩)
      start (.success (.of ())) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_sub_ok c (x + n) st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6» c x ns sts⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · exact rectype_iter6_cons_success_inv c x n ns st sts start finalSupply
  · rintro ⟨middle, hhead, htail⟩
    exact rectype_iter6_cons_success c x n ns st sts start middle finalSupply
      hhead htail

theorem rectype_iter6_left_empty_unmatch (c : SpecTec.context)
    (x start : Nat) (st : SpecTec.subtype)
    (sts : List SpecTec.subtype) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6» c x [] (st :: sts)⟩)
      start .unmatch start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Rectype_ok:rule:iter:6_clauses» c x [] (st :: sts)) ())
    start .unmatch start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Rectype_ok:rule:iter:6:clause:0» c x [] (st :: sts))
      start .unmatch start
    exact SpecTecExecution.Eval.unmatch
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Rectype_ok:rule:iter:6:clause:1» c x [] (st :: sts))
        start .unmatch start
      exact SpecTecExecution.Eval.unmatch
    · exact SpecTecExecution.firstSuccess_nil () start

theorem rectype_iter6_right_empty_unmatch (c : SpecTec.context)
    (x n start : Nat) (ns : List Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Rectype_ok:rule:iter:6» c x (n :: ns) []⟩)
      start .unmatch start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Rectype_ok:rule:iter:6_clauses» c x (n :: ns) []) ())
    start .unmatch start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Rectype_ok:rule:iter:6:clause:0» c x (n :: ns) [])
      start .unmatch start
    exact SpecTecExecution.Eval.unmatch
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«Rectype_ok:rule:iter:6:clause:1» c x (n :: ns) [])
        start .unmatch start
      exact SpecTecExecution.Eval.unmatch
    · exact SpecTecExecution.firstSuccess_nil () start

end properties.wasm_module_not_ok.Rejection
