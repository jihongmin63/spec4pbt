import properties.wasm_module_not_ok.ReftypeSubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

def substValtypeResult (t : SpecTec.valtype)
    (dts : List SpecTec.deftype) : Option SpecTec.valtype :=
  match t with
  | .RefT rt => (substReftypeResult rt dts).map SpecTec.valtype.RefT
  | other => some other

private theorem subst_valtype_num_of_total (nt : SpecTec.numtype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.valtype,
        SpecTec.SpecTecCall.«$subst_valtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» (.NumT nt)⟩)
      start (.success (.of (SpecTec.valtype.NumT nt))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$subst_valtype_clauses» (List SpecTec.deftype) dts
        SpecTec.SpecTecCall.«$subst_of» (.NumT nt)) ())
    start (.success (.of (SpecTec.valtype.NumT nt))) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$subst_valtype:clause:0» (List SpecTec.deftype) dts
      SpecTec.SpecTecCall.«$subst_of» (.NumT nt))
    start (.success (.of (SpecTec.valtype.NumT nt))) start
  unfold SpecTec.«$subst_valtype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true
      (by simp [SpecTec.«exec:match:valtype:NumT»])
  · exact SpecTecExecution.Eval.pure (SpecTec.valtype.NumT nt)

private theorem subst_valtype_vec_of_total (vt : SpecTec.vectype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.valtype,
        SpecTec.SpecTecCall.«$subst_valtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» (.VecT vt)⟩)
      start (.success (.of (SpecTec.valtype.VecT vt))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$subst_valtype_clauses» (List SpecTec.deftype) dts
        SpecTec.SpecTecCall.«$subst_of» (.VecT vt)) ())
    start (.success (.of (SpecTec.valtype.VecT vt))) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$subst_valtype:clause:0» (List SpecTec.deftype) dts
        SpecTec.SpecTecCall.«$subst_of» (.VecT vt)) start .unmatch start
    unfold SpecTec.«$subst_valtype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:valtype:NumT»])
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$subst_valtype:clause:1» (List SpecTec.deftype) dts
        SpecTec.SpecTecCall.«$subst_of» (.VecT vt))
      start (.success (.of (SpecTec.valtype.VecT vt))) start
    unfold SpecTec.«$subst_valtype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true
        (by simp [SpecTec.«exec:match:valtype:VecT»])
    · exact SpecTecExecution.Eval.pure (SpecTec.valtype.VecT vt)

private theorem subst_valtype_bot_of_total
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.valtype,
        SpecTec.SpecTecCall.«$subst_valtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» .BotT⟩)
      start (.success (.of (SpecTec.valtype.BotT))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$subst_valtype_clauses» (List SpecTec.deftype) dts
        SpecTec.SpecTecCall.«$subst_of» .BotT) ())
    start (.success (.of (SpecTec.valtype.BotT))) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$subst_valtype:clause:0» (List SpecTec.deftype) dts
        SpecTec.SpecTecCall.«$subst_of» .BotT) start .unmatch start
    unfold SpecTec.«$subst_valtype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false
      (by simp [SpecTec.«exec:match:valtype:NumT»])
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$subst_valtype:clause:1» (List SpecTec.deftype) dts
          SpecTec.SpecTecCall.«$subst_of» .BotT) start .unmatch start
      unfold SpecTec.«$subst_valtype:clause:1»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:valtype:VecT»])
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_valtype:clause:2» (List SpecTec.deftype) dts
            SpecTec.SpecTecCall.«$subst_of» .BotT) start .unmatch start
        unfold SpecTec.«$subst_valtype:clause:2»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:RefT»])
      · apply SpecTecExecution.firstSuccess_cons_success
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_valtype:clause:3» (List SpecTec.deftype) dts
            SpecTec.SpecTecCall.«$subst_of» .BotT)
          start (.success (.of (SpecTec.valtype.BotT))) start
        unfold SpecTec.«$subst_valtype:clause:3»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · exact SpecTecExecution.Eval.pure SpecTec.valtype.BotT

private theorem subst_valtype_ref_of_total (rt : SpecTec.reftype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.valtype,
        SpecTec.SpecTecCall.«$subst_valtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» (.RefT rt)⟩)
      start (optionOutcome (substValtypeResult (.RefT rt) dts)) start := by
  cases hresult : substReftypeResult rt dts with
  | some rt' =>
      have href : SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨SpecTec.reftype,
            SpecTec.SpecTecCall.«$subst_reftype»
              (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» rt⟩)
          start (.success (.of rt')) start := by
        simpa [optionOutcome, hresult] using subst_reftype_of_total rt dts start
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_valtype_clauses» (List SpecTec.deftype) dts
            SpecTec.SpecTecCall.«$subst_of» (.RefT rt)) ())
        start (optionOutcome (substValtypeResult (.RefT rt) dts)) start
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_valtype:clause:0» (List SpecTec.deftype) dts
            SpecTec.SpecTecCall.«$subst_of» (.RefT rt)) start .unmatch start
        unfold SpecTec.«$subst_valtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:NumT»])
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_valtype:clause:1» (List SpecTec.deftype) dts
              SpecTec.SpecTecCall.«$subst_of» (.RefT rt)) start .unmatch start
          unfold SpecTec.«$subst_valtype:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:valtype:VecT»])
        · simp only [substValtypeResult, hresult, Option.map, optionOutcome]
          apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_valtype:clause:2» (List SpecTec.deftype) dts
              SpecTec.SpecTecCall.«$subst_of» (.RefT rt))
            start (.success (.of (SpecTec.valtype.RefT rt'))) start
          unfold SpecTec.«$subst_valtype:clause:2»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true
              (by simp [SpecTec.«exec:match:valtype:RefT»])
          · apply SpecTecExecution.Eval.bind_success href
            exact SpecTecExecution.Eval.pure (SpecTec.valtype.RefT rt')
  | none =>
      have href : SpecTecExecution.Eval SpecTec.specTecProgram
          (.call ⟨SpecTec.reftype,
            SpecTec.SpecTecCall.«$subst_reftype»
              (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» rt⟩)
          start .unmatch start := by
        simpa [optionOutcome, hresult] using subst_reftype_of_total rt dts start
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$subst_valtype_clauses» (List SpecTec.deftype) dts
            SpecTec.SpecTecCall.«$subst_of» (.RefT rt)) ())
        start (optionOutcome (substValtypeResult (.RefT rt) dts)) start
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$subst_valtype:clause:0» (List SpecTec.deftype) dts
            SpecTec.SpecTecCall.«$subst_of» (.RefT rt)) start .unmatch start
        unfold SpecTec.«$subst_valtype:clause:0»
        apply SpecTecExecution.Eval.bind_unmatch
        exact SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:NumT»])
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$subst_valtype:clause:1» (List SpecTec.deftype) dts
              SpecTec.SpecTecCall.«$subst_of» (.RefT rt)) start .unmatch start
          unfold SpecTec.«$subst_valtype:clause:1»
          apply SpecTecExecution.Eval.bind_unmatch
          exact SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:valtype:VecT»])
        · apply SpecTecExecution.firstSuccess_cons_unmatch
          · change SpecTecExecution.Eval SpecTec.specTecProgram
              (SpecTec.«$subst_valtype:clause:2» (List SpecTec.deftype) dts
                SpecTec.SpecTecCall.«$subst_of» (.RefT rt)) start .unmatch start
            unfold SpecTec.«$subst_valtype:clause:2»
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true
                (by simp [SpecTec.«exec:match:valtype:RefT»])
            · exact SpecTecExecution.Eval.bind_unmatch href
          · simp only [substValtypeResult, hresult, Option.map, optionOutcome]
            apply SpecTecExecution.firstSuccess_cons_unmatch
            · change SpecTecExecution.Eval SpecTec.specTecProgram
                (SpecTec.«$subst_valtype:clause:3» (List SpecTec.deftype) dts
                  SpecTec.SpecTecCall.«$subst_of» (.RefT rt))
                start .unmatch start
              unfold SpecTec.«$subst_valtype:clause:3»
              apply SpecTecExecution.Eval.bind_unmatch
              exact SpecTecExecution.Eval.guard_false (by simp)
            · exact SpecTecExecution.firstSuccess_nil () start

theorem subst_valtype_of_total (t : SpecTec.valtype)
    (dts : List SpecTec.deftype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.valtype,
        SpecTec.SpecTecCall.«$subst_valtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» t⟩)
      start (optionOutcome (substValtypeResult t dts)) start := by
  cases t with
  | NumT nt => simpa [substValtypeResult, optionOutcome] using
      subst_valtype_num_of_total nt dts start
  | VecT vt => simpa [substValtypeResult, optionOutcome] using
      subst_valtype_vec_of_total vt dts start
  | RefT rt => exact subst_valtype_ref_of_total rt dts start
  | BotT => simpa [substValtypeResult, optionOutcome] using
      subst_valtype_bot_of_total dts start

theorem subst_valtype_of_deterministic (t : SpecTec.valtype)
    (dts : List SpecTec.deftype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.valtype,
        SpecTec.SpecTecCall.«$subst_valtype»
          (List SpecTec.deftype) dts SpecTec.SpecTecCall.«$subst_of» t⟩)
      start outcome finalSupply) :
    outcome = optionOutcome (substValtypeResult t dts) ∧
      finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (subst_valtype_of_total t dts start)

end properties.wasm_module_not_ok.Rejection
