import properties.wasm_module_not_ok.MatchResulttypeTrace

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem match_numtype_total (d : List SpecTec.deftype)
    (a b : SpecTec.numtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_numtype» d a b⟩)
      start (.success (.of (decide (a = b)))) start := by
  by_cases heq : a = b
  · apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_numtype_clauses» d a b) ())
      start (.success (.of (decide (a = b)))) start
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_numtype:clause:0» d a b)
      start (.success (.of (decide (a = b)))) start
    unfold SpecTec.«$match_numtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true heq.symm
    · simpa [heq] using
        (SpecTecExecution.Eval.pure true (n := start))
  · apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_numtype_clauses» d a b) ())
      start (.success (.of (decide (a = b)))) start
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_numtype:clause:0» d a b)
        start .unmatch start
      unfold SpecTec.«$match_numtype:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false (by simpa [eq_comm] using heq)
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_numtype:clause:1» d a b)
        start (.success (.of (decide (a = b)))) start
      simpa [SpecTec.«$match_numtype:clause:1», heq] using
        (SpecTecExecution.Eval.pure false (n := start))

theorem match_numtype_deterministic (d : List SpecTec.deftype)
    (a b : SpecTec.numtype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_numtype» d a b⟩)
      start outcome finalSupply) :
    outcome = .success (.of (decide (a = b))) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_numtype_total d a b start)

theorem match_vectype_total (d : List SpecTec.deftype)
    (a b : SpecTec.vectype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_vectype» d a b⟩)
      start (.success (.of (decide (a = b)))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_vectype_clauses» d a b) ())
    start (.success (.of (decide (a = b)))) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_vectype:clause:0» d a b)
    start (.success (.of (decide (a = b)))) start
  exact SpecTecExecution.Eval.pure (decide (a = b))

theorem match_vectype_deterministic (d : List SpecTec.deftype)
    (a b : SpecTec.vectype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_vectype» d a b⟩)
      start outcome finalSupply) :
    outcome = .success (.of (decide (a = b))) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_vectype_total d a b start)

theorem match_packtype_total (d : List SpecTec.deftype)
    (a b : SpecTec.packtype) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_packtype» d a b⟩)
      start (.success (.of (decide (a = b)))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_packtype_clauses» d a b) ())
    start (.success (.of (decide (a = b)))) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_packtype:clause:0» d a b)
    start (.success (.of (decide (a = b)))) start
  exact SpecTecExecution.Eval.pure (decide (a = b))

theorem match_packtype_deterministic (d : List SpecTec.deftype)
    (a b : SpecTec.packtype) (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_packtype» d a b⟩)
      start outcome finalSupply) :
    outcome = .success (.of (decide (a = b))) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (match_packtype_total d a b start)

end properties.wasm_module_not_ok.Rejection
