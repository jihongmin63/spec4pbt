import properties.wasm_module_not_ok.DeftypeSubstOfValidation

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_deftype_substitutions_equal_total
    (d : List SpecTec.deftype) (dt₁ dt₂ a : SpecTec.deftype)
    (start : Nat) (hne : dt₁ ≠ dt₂)
    (hfirst : substDeftypeResult dt₁ d = some a)
    (hsecond : substDeftypeResult dt₂ d = some a) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_deftype» d dt₁ dt₂⟩)
      start (.success (.of true)) start := by
  have hevalFirst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.deftype,
        SpecTec.SpecTecCall.«$subst_deftype»
          (List SpecTec.deftype) d SpecTec.SpecTecCall.«$subst_of» dt₁⟩)
      start (.success (.of a)) start := by
    simpa [optionOutcome, hfirst] using subst_deftype_of_total dt₁ d start
  have hevalSecond : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.deftype,
        SpecTec.SpecTecCall.«$subst_deftype»
          (List SpecTec.deftype) d SpecTec.SpecTecCall.«$subst_of» dt₂⟩)
      start (.success (.of a)) start := by
    simpa [optionOutcome, hsecond] using subst_deftype_of_total dt₂ d start
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_deftype_clauses» d dt₁ dt₂) ())
    start (.success (.of true)) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_deftype:clause:0» d dt₁ dt₂) start .unmatch start
    unfold SpecTec.«$match_deftype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simpa [eq_comm] using hne)
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_deftype:clause:1» d dt₁ dt₂)
      start (.success (.of true)) start
    unfold SpecTec.«$match_deftype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hne
    · apply SpecTecExecution.Eval.bind_success hevalFirst
      apply SpecTecExecution.Eval.bind_success hevalSecond
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.pure true

theorem match_deftype_substitutions_equal_deterministic
    (d : List SpecTec.deftype) (dt₁ dt₂ a : SpecTec.deftype)
    (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (hne : dt₁ ≠ dt₂)
    (hfirst : substDeftypeResult dt₁ d = some a)
    (hsecond : substDeftypeResult dt₂ d = some a)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_deftype» d dt₁ dt₂⟩)
      start outcome finalSupply) :
    outcome = .success (.of true) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_deftype_substitutions_equal_total d dt₁ dt₂ a start hne hfirst hsecond)

theorem match_deftype_first_substitution_none
    (d : List SpecTec.deftype) (dt₁ dt₂ : SpecTec.deftype)
    (start : Nat) (hne : dt₁ ≠ dt₂)
    (hresult : substDeftypeResult dt₁ d = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_deftype» d dt₁ dt₂⟩)
      start .unmatch start := by
  have hfirst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.deftype,
        SpecTec.SpecTecCall.«$subst_deftype»
          (List SpecTec.deftype) d SpecTec.SpecTecCall.«$subst_of» dt₁⟩)
      start .unmatch start := by
    simpa [optionOutcome, hresult] using subst_deftype_of_total dt₁ d start
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$match_deftype_clauses» d dt₁ dt₂) ())
    start .unmatch start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_deftype:clause:0» d dt₁ dt₂) start .unmatch start
    unfold SpecTec.«$match_deftype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simpa [eq_comm] using hne)
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_deftype:clause:1» d dt₁ dt₂) start .unmatch start
      unfold SpecTec.«$match_deftype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true hne
      · exact SpecTecExecution.Eval.bind_unmatch hfirst
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_deftype:clause:2» d dt₁ dt₂) start .unmatch start
        unfold SpecTec.«$match_deftype:clause:2»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hne
        · exact SpecTecExecution.Eval.bind_unmatch hfirst
      · exact SpecTecExecution.firstSuccess_nil () start

theorem match_deftype_second_substitution_none
    (d : List SpecTec.deftype) (dt₁ dt₂ a : SpecTec.deftype)
    (start : Nat) (hne : dt₁ ≠ dt₂)
    (hfirstResult : substDeftypeResult dt₁ d = some a)
    (hsecondResult : substDeftypeResult dt₂ d = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_deftype» d dt₁ dt₂⟩)
      start .unmatch start := by
  have hfirst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.deftype,
        SpecTec.SpecTecCall.«$subst_deftype»
          (List SpecTec.deftype) d SpecTec.SpecTecCall.«$subst_of» dt₁⟩)
      start (.success (.of a)) start := by
    simpa [optionOutcome, hfirstResult] using subst_deftype_of_total dt₁ d start
  have hsecond : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.deftype,
        SpecTec.SpecTecCall.«$subst_deftype»
          (List SpecTec.deftype) d SpecTec.SpecTecCall.«$subst_of» dt₂⟩)
      start .unmatch start := by
    simpa [optionOutcome, hsecondResult] using subst_deftype_of_total dt₂ d start
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$match_deftype_clauses» d dt₁ dt₂) ())
    start .unmatch start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_deftype:clause:0» d dt₁ dt₂) start .unmatch start
    unfold SpecTec.«$match_deftype:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simpa [eq_comm] using hne)
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_deftype:clause:1» d dt₁ dt₂) start .unmatch start
      unfold SpecTec.«$match_deftype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true hne
      · apply SpecTecExecution.Eval.bind_success hfirst
        exact SpecTecExecution.Eval.bind_unmatch hsecond
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_deftype:clause:2» d dt₁ dt₂) start .unmatch start
        unfold SpecTec.«$match_deftype:clause:2»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hne
        · apply SpecTecExecution.Eval.bind_success hfirst
          exact SpecTecExecution.Eval.bind_unmatch hsecond
      · exact SpecTecExecution.firstSuccess_nil () start

end properties.wasm_module_not_ok.Rejection
