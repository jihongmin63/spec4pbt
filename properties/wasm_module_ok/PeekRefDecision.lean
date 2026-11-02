import properties.wasm_module_ok.PeekDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.PeekRefDecision

def peekRefResult : SpecTec.valtype → Option SpecTec.reftype
  | .RefT rt => some rt
  | .BotT => some (.«% %» .NoNull .BotHT)
  | _ => none

theorem peek_ref_total_of_ref
    (n : Nat) (irt : SpecTec.inferresulttype)
    (rt : SpecTec.reftype) (start : Nat)
    (hpeek : PeekDecision.peekResult n irt = .RefT rt) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.reftype, SpecTec.SpecTecCall.«$peek_ref» n irt⟩)
      start (.success (.of rt)) start := by
  rcases irt with ⟨ell, ts⟩
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$peek_ref_clauses» n (ell, ts)) ())
    start (.success (.of rt)) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$peek_ref:clause:0» n (ell, ts))
    start (.success (.of rt)) start
  unfold SpecTec.«$peek_ref:clause:0»
  apply SpecTecExecution.Eval.bind_success
    (PeekDecision.peek_total n (ell, ts) start)
  simp only [hpeek]
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · exact SpecTecExecution.Eval.pure rt

theorem peek_ref_total_of_bot
    (n : Nat) (irt : SpecTec.inferresulttype)
    (start : Nat)
    (hpeek : PeekDecision.peekResult n irt = .BotT) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.reftype, SpecTec.SpecTecCall.«$peek_ref» n irt⟩)
      start (.success (.of (SpecTec.reftype.«% %» .NoNull .BotHT))) start := by
  rcases irt with ⟨ell, ts⟩
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$peek_ref_clauses» n (ell, ts)) ())
    start (.success (.of (SpecTec.reftype.«% %» .NoNull .BotHT))) start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$peek_ref:clause:0» n (ell, ts))
      start .unmatch start
    unfold SpecTec.«$peek_ref:clause:0»
    apply SpecTecExecution.Eval.bind_success
      (PeekDecision.peek_total n (ell, ts) start)
    simp only [hpeek]
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:valtype:RefT»])
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$peek_ref:clause:1» n (ell, ts))
      start (.success (.of (SpecTec.reftype.«% %» .NoNull .BotHT))) start
    unfold SpecTec.«$peek_ref:clause:1»
    apply SpecTecExecution.Eval.bind_success
      (PeekDecision.peek_total n (ell, ts) start)
    simp only [hpeek]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true (by simp)
    · exact SpecTecExecution.Eval.pure _

theorem peek_ref_total_of_some
    (n : Nat) (irt : SpecTec.inferresulttype)
    (rt : SpecTec.reftype) (start : Nat)
    (h : peekRefResult (PeekDecision.peekResult n irt) = some rt) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.reftype, SpecTec.SpecTecCall.«$peek_ref» n irt⟩)
      start (.success (.of rt)) start := by
  cases hv : PeekDecision.peekResult n irt with
  | NumT nt => simp [peekRefResult, hv] at h
  | VecT vt => simp [peekRefResult, hv] at h
  | RefT actual =>
    simp [peekRefResult, hv] at h
    cases h
    exact peek_ref_total_of_ref n irt rt start hv
  | BotT =>
    simp [peekRefResult, hv] at h
    cases h
    exact peek_ref_total_of_bot n irt start hv

theorem peek_ref_unmatch_of_none
    (n : Nat) (irt : SpecTec.inferresulttype) (start : Nat)
    (h : peekRefResult (PeekDecision.peekResult n irt) = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.reftype, SpecTec.SpecTecCall.«$peek_ref» n irt⟩)
      start .unmatch start := by
  have hnotref :
      SpecTec.«exec:match:valtype:RefT»
        (PeekDecision.peekResult n irt) ≠ true := by
    cases hv : PeekDecision.peekResult n irt <;>
      simp [peekRefResult, hv, SpecTec.«exec:match:valtype:RefT»] at h ⊢
  have hnotbot :
      SpecTec.valtype.BotT ≠ PeekDecision.peekResult n irt := by
    cases hv : PeekDecision.peekResult n irt <;>
      simp [peekRefResult, hv] at h ⊢
  rcases irt with ⟨ell, ts⟩
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$peek_ref_clauses» n (ell, ts)) ())
    start .unmatch start
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$peek_ref:clause:0» n (ell, ts)) start .unmatch start
    unfold SpecTec.«$peek_ref:clause:0»
    apply SpecTecExecution.Eval.bind_success
      (PeekDecision.peek_total n (ell, ts) start)
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false hnotref
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$peek_ref:clause:1» n (ell, ts)) start .unmatch start
      unfold SpecTec.«$peek_ref:clause:1»
      apply SpecTecExecution.Eval.bind_success
        (PeekDecision.peek_total n (ell, ts) start)
      apply SpecTecExecution.Eval.bind_unmatch
      exact SpecTecExecution.Eval.guard_false hnotbot
    · exact SpecTecExecution.firstSuccess_nil () start

theorem peek_ref_success_iff_result
    (n : Nat) (irt : SpecTec.inferresulttype)
    (rt : SpecTec.reftype) (start fin : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.reftype, SpecTec.SpecTecCall.«$peek_ref» n irt⟩)
      start (.success (.of rt)) fin ↔
    peekRefResult (PeekDecision.peekResult n irt) = some rt ∧
      fin = start := by
  constructor
  · intro heval
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    cases hopt : peekRefResult (PeekDecision.peekResult n irt) with
    | none =>
      obtain ⟨hout, _⟩ := SpecTecExecution.eval_deterministic hdet heval
        (peek_ref_unmatch_of_none n irt start hopt)
      cases hout
    | some actual =>
      obtain ⟨hout, hsupply⟩ := SpecTecExecution.eval_deterministic hdet
        heval (peek_ref_total_of_some n irt actual start hopt)
      cases hout
      exact ⟨by simpa [hopt], hsupply⟩
  · rintro ⟨hopt, rfl⟩
    exact peek_ref_total_of_some n irt rt fin hopt

end properties.wasm_module_ok.PeekRefDecision
