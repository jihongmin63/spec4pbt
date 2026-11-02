import properties.wasm_module_ok.ValtypeValidation
import properties.wasm_module_not_ok.SubtypeValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem resulttype_iter0_nil_success (c : SpecTec.context) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Resulttype_ok:rule:iter:0» c []⟩)
      start (.success (.of ())) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Resulttype_ok:rule:iter:0_clauses» c []) ())
    start (.success (.of ())) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Resulttype_ok:rule:iter:0:clause:0» c [])
    start (.success (.of ())) start
  exact SpecTecExecution.Eval.pure ()

theorem resulttype_iter0_cons_success (c : SpecTec.context)
    (st : SpecTec.valtype) (sts : List SpecTec.valtype)
    (start middle finalSupply : Nat)
    (hhead : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Valtype_ok c st⟩)
      start (.success (.of ())) middle)
    (htail : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Resulttype_ok:rule:iter:0» c sts⟩)
      middle (.success (.of ())) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Resulttype_ok:rule:iter:0» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Resulttype_ok:rule:iter:0_clauses» c (st :: sts)) ())
    start (.success (.of ())) finalSupply
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Resulttype_ok:rule:iter:0:clause:0» c (st :: sts))
      start .unmatch start
    exact SpecTecExecution.Eval.unmatch
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Resulttype_ok:rule:iter:0:clause:1» c (st :: sts))
      start (.success (.of ())) finalSupply
    unfold SpecTec.«Resulttype_ok:rule:iter:0:clause:1»
    apply SpecTecExecution.Eval.bind_success hhead
    apply SpecTecExecution.Eval.bind_success htail
    exact SpecTecExecution.Eval.pure ()

theorem resulttype_iter0_cons_success_inv (c : SpecTec.context)
    (st : SpecTec.valtype) (sts : List SpecTec.valtype)
    (start finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Resulttype_ok:rule:iter:0» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply) :
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Valtype_ok c st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Resulttype_ok:rule:iter:0» c sts⟩)
        middle (.success (.of ())) finalSupply := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Resulttype_ok:rule:iter:0_clauses» c (st :: sts)) ())
      start (.success (.of ())) finalSupply at hbody
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (.orElse (SpecTec.«Resulttype_ok:rule:iter:0:clause:0» c (st :: sts))
        (fun _ => SpecTecExecution.firstSuccess
          [fun _ => SpecTec.«Resulttype_ok:rule:iter:0:clause:1» c (st :: sts)] ()))
      start (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      change SpecTecExecution.Eval SpecTec.specTecProgram .unmatch
        start (.success (.of ())) finalSupply at hfirst
      cases hfirst
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Resulttype_ok:rule:iter:0:clause:1» c (st :: sts))
          (fun _ => .unmatch))
        start (.success (.of ())) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Resulttype_ok:rule:iter:0:clause:1» at hsecond
        cases hsecond with
        | bind_success hhead hrest =>
          cases hrest with
          | bind_success htail hpure =>
            cases hpure with
            | pure => exact ⟨_, hhead, htail⟩
      | orElse_unmatch _ hlast => cases hlast

theorem resulttype_iter0_cons_success_iff (c : SpecTec.context)
    (st : SpecTec.valtype) (sts : List SpecTec.valtype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Resulttype_ok:rule:iter:0» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Valtype_ok c st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Resulttype_ok:rule:iter:0» c sts⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · exact resulttype_iter0_cons_success_inv c st sts start finalSupply
  · rintro ⟨middle, hhead, htail⟩
    exact resulttype_iter0_cons_success c st sts start middle finalSupply hhead htail

def resulttypesValid (c : SpecTec.context)
    (ts : List SpecTec.valtype) : Bool :=
  ts.all (properties.wasm_module_ok.ValtypeValidation.valtypeValid c)

theorem resulttype_iter0_success_iff_valid (c : SpecTec.context)
    (ts : List SpecTec.valtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Resulttype_ok:rule:iter:0» c ts⟩)
      start (.success (.of ())) finalSupply ↔
    resulttypesValid c ts = true ∧ finalSupply = start := by
  induction ts generalizing start finalSupply with
  | nil =>
      constructor
      · intro h
        obtain ⟨_, hfinal⟩ :=
          SpecTecExecution.eval_deterministic program_primitive_deterministic h
            (resulttype_iter0_nil_success c start)
        exact ⟨rfl, hfinal⟩
      · rintro ⟨_, rfl⟩
        exact resulttype_iter0_nil_success c finalSupply
  | cons t ts ih =>
      constructor
      · intro h
        obtain ⟨middle, hhead, htail⟩ :=
          (resulttype_iter0_cons_success_iff c t ts start finalSupply).1 h
        obtain ⟨hvalid, hmiddle⟩ :=
          (properties.wasm_module_ok.ValtypeValidation.valtype_success_iff_valid
            c t start middle).1 hhead
        obtain ⟨hrest, hfinal⟩ := (ih middle finalSupply).1 htail
        constructor
        · simpa [resulttypesValid, hvalid] using hrest
        · omega
      · rintro ⟨hall, rfl⟩
        have hsplit :
            properties.wasm_module_ok.ValtypeValidation.valtypeValid c t = true ∧
              resulttypesValid c ts = true := by
          simpa [resulttypesValid] using hall
        have hhead :=
          (properties.wasm_module_ok.ValtypeValidation.valtype_success_iff_valid
            c t finalSupply finalSupply).2 ⟨hsplit.1, rfl⟩
        have htail := (ih finalSupply finalSupply).2 ⟨hsplit.2, rfl⟩
        exact resulttype_iter0_cons_success c t ts
          finalSupply finalSupply finalSupply hhead htail

end properties.wasm_module_not_ok.Rejection
