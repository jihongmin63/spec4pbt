import properties.wasm_module_not_ok.Rejection

set_option autoImplicit false
namespace properties.wasm_module_not_ok.Rejection

theorem types_ok_nil_success (c : SpecTec.context) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Types_ok c []⟩)
      start (.success (.of c)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Types_ok_clauses c []) ())
    start (.success (.of c)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Types_ok:clause:0» c []) start .unmatch start
    unfold SpecTec.«Types_ok:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    simp
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Types_ok:clause:1» c []) start (.success (.of c)) start
    unfold SpecTec.«Types_ok:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      simp
    · exact SpecTecExecution.Eval.pure c


theorem types_ok_cons_success (c c1 c2 : SpecTec.context)
    (t : SpecTec.type) (ts : List SpecTec.type)
    (start middle finalSupply : Nat)
    (ht : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Type_ok c t⟩)
      start (.success (.of c1)) middle)
    (hrest : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Types_ok c1 ts⟩)
      middle (.success (.of c2)) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Types_ok c (t :: ts)⟩)
      start (.success (.of c2)) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.Types_ok_clauses c (t :: ts)) ())
    start (.success (.of c2)) finalSupply
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Types_ok:clause:0» c (t :: ts))
    start (.success (.of c2)) finalSupply
  unfold SpecTec.«Types_ok:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · apply SpecTecExecution.Eval.guard_true
    simp
  · apply SpecTecExecution.Eval.bind_success ht
    apply SpecTecExecution.Eval.bind_success hrest
    exact SpecTecExecution.Eval.pure c2


theorem types_ok_cons_success_inv (c c2 : SpecTec.context)
    (t : SpecTec.type) (ts : List SpecTec.type)
    (start finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Types_ok c (t :: ts)⟩)
      start (.success (.of c2)) finalSupply) :
    ∃ (c1 : SpecTec.context) (middle : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Type_ok c t⟩)
        start (.success (.of c1)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Types_ok c1 ts⟩)
        middle (.success (.of c2)) finalSupply := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Types_ok_clauses c (t :: ts)) ())
      start (.success (.of c2)) finalSupply at hbody
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (.orElse (SpecTec.«Types_ok:clause:0» c (t :: ts))
        (fun _ => SpecTecExecution.firstSuccess
          [fun _ => SpecTec.«Types_ok:clause:1» c (t :: ts)] ()))
      start (.success (.of c2)) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«Types_ok:clause:0» at hfirst
      cases hfirst with
      | bind_success hguard htail =>
        cases hguard with
        | guard_true _ =>
          cases htail with
          | bind_success ht htail =>
            cases htail with
            | bind_success hrest hpure =>
              cases hpure with
              | pure => exact ⟨_, _, ht, hrest⟩
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Types_ok:clause:1» c (t :: ts))
          (fun _ => .unmatch))
        start (.success (.of c2)) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Types_ok:clause:1» at hsecond
        cases hsecond with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond => simp at hcond
      | orElse_unmatch _ hlast => cases hlast


theorem types_ok_nil_deterministic (c : SpecTec.context) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Types_ok c []⟩)
      start outcome finalSupply) :
    outcome = .success (.of c) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (types_ok_nil_success c start)

theorem types_ok_cons_success_iff (c c2 : SpecTec.context)
    (t : SpecTec.type) (ts : List SpecTec.type)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Types_ok c (t :: ts)⟩)
      start (.success (.of c2)) finalSupply ↔
    ∃ (c1 : SpecTec.context) (middle : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Type_ok c t⟩)
        start (.success (.of c1)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Types_ok c1 ts⟩)
        middle (.success (.of c2)) finalSupply := by
  constructor
  · exact types_ok_cons_success_inv c c2 t ts start finalSupply
  · rintro ⟨c1, middle, ht, hrest⟩
    exact types_ok_cons_success c c1 c2 t ts start middle finalSupply ht hrest

theorem type_ok_success_iff_rectype_ok (c c1 : SpecTec.context)
    (t : SpecTec.type) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Type_ok c t⟩)
      start (.success (.of c1)) finalSupply ↔
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.Rectype_ok c t⟩)
      start (.success (.of c1)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess (SpecTec.Type_ok_clauses c t) ())
        start (.success (.of c1)) finalSupply at hbody
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Type_ok:clause:0» c t) (fun _ => .unmatch))
        start (.success (.of c1)) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«Type_ok:clause:0» at hclause
        cases hclause with
        | bind_success hrect hpure =>
          cases hpure with
          | pure => exact hrect
      | orElse_unmatch _ htail => cases htail
  · intro hrect
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.Type_ok_clauses c t) ())
      start (.success (.of c1)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Type_ok:clause:0» c t)
      start (.success (.of c1)) finalSupply
    unfold SpecTec.«Type_ok:clause:0»
    exact SpecTecExecution.Eval.bind_success hrect (.pure c1)


end properties.wasm_module_not_ok.Rejection
