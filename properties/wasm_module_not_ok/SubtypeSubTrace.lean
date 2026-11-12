import properties.wasm_module_not_ok.RectypeIterDecision

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem subtype_sub_iter0_nil_success (c : SpecTec.context) (x : Nat) (strt : SpecTec.strtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_sub_ok:rule:iter:0» c x strt []⟩)
      start (.success (.of ())) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» c x strt []) ())
    start (.success (.of ())) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Subtype_sub_ok:rule:iter:0:clause:0» c x strt [])
    start (.success (.of ())) start
  exact SpecTecExecution.Eval.pure ()

theorem subtype_sub_iter0_cons_success (c : SpecTec.context) (x : Nat) (strt : SpecTec.strtype)
    (st : SpecTec.heaptype) (sts : List SpecTec.heaptype)
    (start middle finalSupply : Nat)
    (hhead : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_sub_ok' c x strt st⟩)
      start (.success (.of ())) middle)
    (htail : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_sub_ok:rule:iter:0» c x strt sts⟩)
      middle (.success (.of ())) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_sub_ok:rule:iter:0» c x strt (st :: sts)⟩)
      start (.success (.of ())) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» c x strt (st :: sts)) ())
    start (.success (.of ())) finalSupply
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Subtype_sub_ok:rule:iter:0:clause:0» c x strt (st :: sts))
      start .unmatch start
    exact SpecTecExecution.Eval.unmatch
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Subtype_sub_ok:rule:iter:0:clause:1» c x strt (st :: sts))
      start (.success (.of ())) finalSupply
    unfold SpecTec.«Subtype_sub_ok:rule:iter:0:clause:1»
    apply SpecTecExecution.Eval.bind_success hhead
    apply SpecTecExecution.Eval.bind_success htail
    exact SpecTecExecution.Eval.pure ()

theorem subtype_sub_iter0_cons_success_inv (c : SpecTec.context) (x : Nat) (strt : SpecTec.strtype)
    (st : SpecTec.heaptype) (sts : List SpecTec.heaptype)
    (start finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_sub_ok:rule:iter:0» c x strt (st :: sts)⟩)
      start (.success (.of ())) finalSupply) :
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_sub_ok' c x strt st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Subtype_sub_ok:rule:iter:0» c x strt sts⟩)
        middle (.success (.of ())) finalSupply := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» c x strt (st :: sts)) ())
      start (.success (.of ())) finalSupply at hbody
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (.orElse (SpecTec.«Subtype_sub_ok:rule:iter:0:clause:0» c x strt (st :: sts))
        (fun _ => SpecTecExecution.firstSuccess
          [fun _ => SpecTec.«Subtype_sub_ok:rule:iter:0:clause:1» c x strt (st :: sts)] ()))
      start (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      change SpecTecExecution.Eval SpecTec.specTecProgram .unmatch
        start (.success (.of ())) finalSupply at hfirst
      cases hfirst
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Subtype_sub_ok:rule:iter:0:clause:1» c x strt (st :: sts))
          (fun _ => .unmatch))
        start (.success (.of ())) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Subtype_sub_ok:rule:iter:0:clause:1» at hsecond
        cases hsecond with
        | bind_success hhead hrest =>
          cases hrest with
          | bind_success htail hpure =>
            cases hpure with
            | pure => exact ⟨_, hhead, htail⟩
      | orElse_unmatch _ hlast => cases hlast

theorem subtype_sub_iter0_cons_success_iff (c : SpecTec.context) (x : Nat) (strt : SpecTec.strtype)
    (st : SpecTec.heaptype) (sts : List SpecTec.heaptype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_sub_ok:rule:iter:0» c x strt (st :: sts)⟩)
      start (.success (.of ())) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Subtype_sub_ok' c x strt st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Subtype_sub_ok:rule:iter:0» c x strt sts⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · exact subtype_sub_iter0_cons_success_inv c x strt st sts start finalSupply
  · rintro ⟨middle, hhead, htail⟩
    exact subtype_sub_iter0_cons_success c x strt st sts start middle finalSupply hhead htail

theorem subtype_sub_success_iff (c : SpecTec.context) (x : Nat)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_sub_ok c x (.SubT fin hts strt)⟩)
      start (.success (.of ())) finalSupply ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_sub_ok:rule:iter:0» c x strt hts⟩)
      start (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.Subtype_sub_ok_clauses c x (.SubT fin hts strt)) ())
        start (.success (.of ())) finalSupply at hbody
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Subtype_sub_ok:clause:0» c x (.SubT fin hts strt))
          (fun _ => .unmatch))
        start (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Subtype_sub_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hiter hpure =>
          cases hpure with
          | pure => exact hiter
      | orElse_unmatch _ htail => cases htail
  · intro hiter
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Subtype_sub_ok_clauses c x (.SubT fin hts strt)) ())
      start (.success (.of ())) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Subtype_sub_ok:clause:0» c x (.SubT fin hts strt))
      start (.success (.of ())) finalSupply
    unfold SpecTec.«Subtype_sub_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success hiter
    exact SpecTecExecution.Eval.pure ()


end properties.wasm_module_not_ok.Rejection
