import properties.wasm_module_not_ok.FieldtypeValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem structtype_iter0_nil_success (c : SpecTec.context) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Structtype_ok:rule:iter:0» c []⟩)
      start (.success (.of ())) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Structtype_ok:rule:iter:0_clauses» c []) ())
    start (.success (.of ())) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«Structtype_ok:rule:iter:0:clause:0» c [])
    start (.success (.of ())) start
  exact SpecTecExecution.Eval.pure ()

theorem structtype_iter0_cons_success (c : SpecTec.context)
    (st : SpecTec.fieldtype) (sts : List SpecTec.fieldtype)
    (start middle finalSupply : Nat)
    (hhead : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Fieldtype_ok c st⟩)
      start (.success (.of ())) middle)
    (htail : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Structtype_ok:rule:iter:0» c sts⟩)
      middle (.success (.of ())) finalSupply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Structtype_ok:rule:iter:0» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«Structtype_ok:rule:iter:0_clauses» c (st :: sts)) ())
    start (.success (.of ())) finalSupply
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Structtype_ok:rule:iter:0:clause:0» c (st :: sts))
      start .unmatch start
    exact SpecTecExecution.Eval.unmatch
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«Structtype_ok:rule:iter:0:clause:1» c (st :: sts))
      start (.success (.of ())) finalSupply
    unfold SpecTec.«Structtype_ok:rule:iter:0:clause:1»
    apply SpecTecExecution.Eval.bind_success hhead
    apply SpecTecExecution.Eval.bind_success htail
    exact SpecTecExecution.Eval.pure ()

theorem structtype_iter0_cons_success_inv (c : SpecTec.context)
    (st : SpecTec.fieldtype) (sts : List SpecTec.fieldtype)
    (start finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Structtype_ok:rule:iter:0» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply) :
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Fieldtype_ok c st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Structtype_ok:rule:iter:0» c sts⟩)
        middle (.success (.of ())) finalSupply := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«Structtype_ok:rule:iter:0_clauses» c (st :: sts)) ())
      start (.success (.of ())) finalSupply at hbody
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (.orElse (SpecTec.«Structtype_ok:rule:iter:0:clause:0» c (st :: sts))
        (fun _ => SpecTecExecution.firstSuccess
          [fun _ => SpecTec.«Structtype_ok:rule:iter:0:clause:1» c (st :: sts)] ()))
      start (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      change SpecTecExecution.Eval SpecTec.specTecProgram .unmatch
        start (.success (.of ())) finalSupply at hfirst
      cases hfirst
    | orElse_unmatch _ htail =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«Structtype_ok:rule:iter:0:clause:1» c (st :: sts))
          (fun _ => .unmatch))
        start (.success (.of ())) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Structtype_ok:rule:iter:0:clause:1» at hsecond
        cases hsecond with
        | bind_success hhead hrest =>
          cases hrest with
          | bind_success htail hpure =>
            cases hpure with
            | pure => exact ⟨_, hhead, htail⟩
      | orElse_unmatch _ hlast => cases hlast

theorem structtype_iter0_cons_success_iff (c : SpecTec.context)
    (st : SpecTec.fieldtype) (sts : List SpecTec.fieldtype)
    (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Structtype_ok:rule:iter:0» c (st :: sts)⟩)
      start (.success (.of ())) finalSupply ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit, SpecTec.SpecTecCall.Fieldtype_ok c st⟩)
        start (.success (.of ())) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«Structtype_ok:rule:iter:0» c sts⟩)
        middle (.success (.of ())) finalSupply := by
  constructor
  · exact structtype_iter0_cons_success_inv c st sts start finalSupply
  · rintro ⟨middle, hhead, htail⟩
    exact structtype_iter0_cons_success c st sts start middle finalSupply hhead htail

def fieldtypesValid (c : SpecTec.context)
    (ts : List SpecTec.fieldtype) : Bool :=
  ts.all (fieldtypeValid c)

theorem structtype_iter0_success_iff_valid (c : SpecTec.context)
    (ts : List SpecTec.fieldtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Structtype_ok:rule:iter:0» c ts⟩)
      start (.success (.of ())) finalSupply ↔
    fieldtypesValid c ts = true ∧ finalSupply = start := by
  induction ts generalizing start finalSupply with
  | nil =>
      constructor
      · intro h
        obtain ⟨_, hfinal⟩ :=
          SpecTecExecution.eval_deterministic program_primitive_deterministic h
            (structtype_iter0_nil_success c start)
        exact ⟨rfl, hfinal⟩
      · rintro ⟨_, rfl⟩
        exact structtype_iter0_nil_success c finalSupply
  | cons t ts ih =>
      constructor
      · intro h
        obtain ⟨middle, hhead, htail⟩ :=
          (structtype_iter0_cons_success_iff c t ts start finalSupply).1 h
        obtain ⟨hvalid, hmiddle⟩ :=
          (fieldtype_ok_success_iff_valid
            c t start middle).1 hhead
        obtain ⟨hrest, hfinal⟩ := (ih middle finalSupply).1 htail
        constructor
        · simpa [fieldtypesValid, hvalid] using hrest
        · omega
      · rintro ⟨hall, rfl⟩
        have hsplit :
            fieldtypeValid c t = true ∧
              fieldtypesValid c ts = true := by
          simpa [fieldtypesValid] using hall
        have hhead :=
          (fieldtype_ok_success_iff_valid
            c t finalSupply finalSupply).2 ⟨hsplit.1, rfl⟩
        have htail := (ih finalSupply finalSupply).2 ⟨hsplit.2, rfl⟩
        exact structtype_iter0_cons_success c t ts
          finalSupply finalSupply finalSupply hhead htail

def structtypeValid (c : SpecTec.context)
    (st : SpecTec.structtype) : Bool :=
  match st with
  | .StructT ys => fieldtypesValid c ys

theorem structtype_ok_success_iff_valid (c : SpecTec.context)
    (st : SpecTec.structtype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Structtype_ok c st⟩)
      start (.success (.of ())) finalSupply ↔
    structtypeValid c st = true ∧ finalSupply = start := by
  cases st with
  | StructT ys =>
      constructor
      · intro h
        cases h with
        | call hbody =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Structtype_ok:clause:0» c (.StructT ys))
              (fun _ => .unmatch))
            start (.success (.of ())) finalSupply at hbody
          cases hbody with
          | orElse_success hfirst =>
            unfold SpecTec.«Structtype_ok:clause:0» at hfirst
            cases hfirst with
            | bind_success hiter hpure =>
              cases hpure with
              | pure =>
                simpa [structtypeValid] using
                  (structtype_iter0_success_iff_valid c ys start finalSupply).1 hiter
          | orElse_unmatch _ htail => cases htail
      · rintro ⟨hvalid, rfl⟩
        have hiter :=
          (structtype_iter0_success_iff_valid c ys finalSupply finalSupply).2
            ⟨by simpa [structtypeValid] using hvalid, rfl⟩
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Structtype_ok_clauses c (.StructT ys)) ())
          finalSupply (.success (.of ())) finalSupply
        apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Structtype_ok:clause:0» c (.StructT ys))
          finalSupply (.success (.of ())) finalSupply
        unfold SpecTec.«Structtype_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success hiter
        exact SpecTecExecution.Eval.pure ()

def arraytypeValid (c : SpecTec.context)
    (arrayTy : SpecTec.arraytype) : Bool :=
  match arrayTy with
  | .ArrayT yt => fieldtypeValid c yt

theorem arraytype_ok_success_iff_valid (c : SpecTec.context)
    (arrayTy : SpecTec.arraytype) (start finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Arraytype_ok c arrayTy⟩)
      start (.success (.of ())) finalSupply ↔
    arraytypeValid c arrayTy = true ∧ finalSupply = start := by
  cases arrayTy with
  | ArrayT yt =>
      constructor
      · intro h
        cases h with
        | call hbody =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.orElse (SpecTec.«Arraytype_ok:clause:0» c (.ArrayT yt))
              (fun _ => .unmatch))
            start (.success (.of ())) finalSupply at hbody
          cases hbody with
          | orElse_success hfirst =>
            unfold SpecTec.«Arraytype_ok:clause:0» at hfirst
            cases hfirst with
            | bind_success hfield hpure =>
              cases hpure with
              | pure =>
                simpa [arraytypeValid] using
                  (fieldtype_ok_success_iff_valid c yt start finalSupply).1 hfield
          | orElse_unmatch _ htail => cases htail
      · rintro ⟨hvalid, rfl⟩
        have hfield :=
          (fieldtype_ok_success_iff_valid c yt finalSupply finalSupply).2
            ⟨by simpa [arraytypeValid] using hvalid, rfl⟩
        apply SpecTecExecution.Eval.call
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTecExecution.firstSuccess
            (SpecTec.Arraytype_ok_clauses c (.ArrayT yt)) ())
          finalSupply (.success (.of ())) finalSupply
        apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«Arraytype_ok:clause:0» c (.ArrayT yt))
          finalSupply (.success (.of ())) finalSupply
        unfold SpecTec.«Arraytype_ok:clause:0»
        apply SpecTecExecution.Eval.bind_success hfield
        exact SpecTecExecution.Eval.pure ()

end properties.wasm_module_not_ok.Rejection
