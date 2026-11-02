import properties.wasm_module_not_ok.UnrolldtValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem subtype_iter0_nil_success (c : SpecTec.context) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c []⟩)
      start (.success (.of ())) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Subtype_ok:rule:iter:0_clauses» c []) ())
    start (.success (.of ())) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Subtype_ok:rule:iter:0:clause:0» c [])
    start (.success (.of ())) start
  exact SpecTecExecution.Eval.pure ()

theorem subtype_iter0_cons_success (c : SpecTec.context)
    (st : SpecTec.heaptype) (sts : List SpecTec.heaptype)
    (start middle finalSupply : Nat)
    (hhead : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Heaptype_ok c st⟩)
      start (.success (.of ())) middle)
    (htail : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c sts⟩)
      middle (.success (.of ())) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Subtype_ok:rule:iter:0_clauses» c (st :: sts)) ())
    start (.success (.of ())) finalSupply
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Subtype_ok:rule:iter:0:clause:0» c (st :: sts))
      start .unmatch start
    exact SpecTecExecution.Eval.unmatch
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Subtype_ok:rule:iter:0:clause:1» c (st :: sts))
      start (.success (.of ())) finalSupply
    unfold SpecTec.«Subtype_ok:rule:iter:0:clause:1»
    apply SpecTecExecution.Eval.bind_success hhead
    apply SpecTecExecution.Eval.bind_success htail
    exact SpecTecExecution.Eval.pure ()

theorem subtype_iter0_cons_success_inv (c : SpecTec.context)
    (st : SpecTec.heaptype) (sts : List SpecTec.heaptype)
    (start finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply) :
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Heaptype_ok c st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c sts⟩)
        middle (.success (.of ())) finalSupply := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Subtype_ok:rule:iter:0_clauses» c (st :: sts)) ())
      start (.success (.of ())) finalSupply at hbody
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (.orElse (SpecTec.«Subtype_ok:rule:iter:0:clause:0» c (st :: sts))
        (fun _ => SpecTecExecution.firstSuccess
          [fun _ => SpecTec.«Subtype_ok:rule:iter:0:clause:1» c (st :: sts)] ()))
      start (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      change SpecTecExecution.Eval SpecTec.specTecProgram .unmatch
        start (.success (.of ())) finalSupply at hfirst
      cases hfirst
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Subtype_ok:rule:iter:0:clause:1» c (st :: sts))
          (fun _ => .unmatch))
        start (.success (.of ())) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Subtype_ok:rule:iter:0:clause:1» at hsecond
        cases hsecond with
        | bind_success hhead hrest =>
          cases hrest with
          | bind_success htail hpure =>
            cases hpure with
            | pure => exact ⟨_, hhead, htail⟩
      | orElse_unmatch _ hlast => cases hlast

theorem subtype_iter0_cons_success_iff (c : SpecTec.context)
    (st : SpecTec.heaptype) (sts : List SpecTec.heaptype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Heaptype_ok c st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c sts⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · exact subtype_iter0_cons_success_inv c st sts start finalSupply
  · rintro ⟨middle, hhead, htail⟩
    exact subtype_iter0_cons_success c st sts start middle finalSupply hhead htail

theorem subtype_ok_success_iff (c : SpecTec.context)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_ok c (.SubT fin hts strt)⟩)
      start (.success (.of ())) finalSupply ↔
    hts.length ≤ 1 ∧
      ∃ middle : Nat,
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit,
            SpecTec.SpecTecCall.«Subtype_ok:rule:iter:0» c hts⟩)
          start (.success (.of ())) middle ∧
        SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨Unit, SpecTec.SpecTecCall.Strtype_ok c strt⟩)
          middle (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.Subtype_ok_clauses c (.SubT fin hts strt)) ())
        start (.success (.of ())) finalSupply at hbody
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Subtype_ok:clause:0» c (.SubT fin hts strt))
          (fun _ => .unmatch))
        start (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Subtype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard hrest =>
          cases hguard with
          | guard_true hlen =>
            cases hrest with
            | bind_success hiter hrest =>
              cases hrest with
              | bind_success hstr hpure =>
                cases hpure with
                | pure => exact ⟨hlen, _, hiter, hstr⟩
      | orElse_unmatch _ htail => cases htail
  · rintro ⟨hlen, middle, hiter, hstr⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.Subtype_ok_clauses c (.SubT fin hts strt)) ())
      start (.success (.of ())) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Subtype_ok:clause:0» c (.SubT fin hts strt))
      start (.success (.of ())) finalSupply
    unfold SpecTec.«Subtype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hlen
    · apply SpecTecExecution.Eval.bind_success hiter
      apply SpecTecExecution.Eval.bind_success hstr
      exact SpecTecExecution.Eval.pure ()

theorem subtype_ok_length_unmatch (c : SpecTec.context)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (start : Nat)
    (hlen : 1 < hts.length) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Subtype_ok c (.SubT fin hts strt)⟩)
      start .unmatch start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.Subtype_ok_clauses c (.SubT fin hts strt)) ())
    start .unmatch start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Subtype_ok:clause:0» c (.SubT fin hts strt))
      start .unmatch start
    unfold SpecTec.«Subtype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by omega)
  · exact SpecTecExecution.firstSuccess_nil () start

end properties.wasm_module_not_ok.Rejection
