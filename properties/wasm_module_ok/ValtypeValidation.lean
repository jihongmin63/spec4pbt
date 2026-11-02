import properties.wasm_module_ok.HeaptypeValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ValtypeValidation

theorem numtype_total (c : SpecTec.context) (t : SpecTec.numtype)
    (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Numtype_ok c t⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Numtype_ok_clauses c t))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_success
  exact SpecTecExecution.Eval.pure ()

theorem vectype_total (c : SpecTec.context) (t : SpecTec.vectype)
    (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Vectype_ok c t⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.Vectype_ok_clauses c t))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_success
  exact SpecTecExecution.Eval.pure ()

theorem valtype_num_total (c : SpecTec.context)
    (t : SpecTec.numtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Valtype_ok c (.NumT t)⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.Valtype_ok_clauses c (.NumT t)))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Valtype_ok:clause:0» c (.NumT t))
    n (.success (.of ())) n
  unfold SpecTec.«Valtype_ok:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · apply SpecTecExecution.Eval.guard_true
    rfl
  · apply SpecTecExecution.Eval.bind_success (numtype_total c t n)
    exact SpecTecExecution.Eval.pure ()

theorem valtype_vec_total (c : SpecTec.context)
    (t : SpecTec.vectype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Valtype_ok c (.VecT t)⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.Valtype_ok_clauses c (.VecT t)))
    n (.success (.of ())) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Valtype_ok:clause:0» c (.VecT t)) n .unmatch n
    unfold SpecTec.«Valtype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    simp [SpecTec.«exec:match:valtype:NumT»]
  · apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Valtype_ok:clause:1» c (.VecT t))
      n (.success (.of ())) n
    unfold SpecTec.«Valtype_ok:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      rfl
    · apply SpecTecExecution.Eval.bind_success (vectype_total c t n)
      exact SpecTecExecution.Eval.pure ()

theorem reftype_success_iff (c : SpecTec.context)
    (null : SpecTec.null) (ht : SpecTec.heaptype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Reftype_ok
        c (.«% %» null ht)⟩)
      n (.success (.of ())) finalSupply ↔
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Heaptype_ok c ht⟩)
      n (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Reftype_ok:clause:0» c (.«% %» null ht))
          (fun _ => .unmatch))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«Reftype_ok:clause:0» at hclause
        cases hclause with
        | bind_success hheap hpure =>
          cases hpure with
          | pure => exact hheap
      | orElse_unmatch hfailedSupply hlast => restore_supply hfailedSupply at hlast; cases hlast
  · intro hheap
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Reftype_ok_clauses c (.«% %» null ht)))
      n (.success (.of ())) finalSupply
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Reftype_ok:clause:0» c (.«% %» null ht))
      n (.success (.of ())) finalSupply
    unfold SpecTec.«Reftype_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success hheap
    exact SpecTecExecution.Eval.pure ()

theorem valtype_ref_success_iff (c : SpecTec.context)
    (null : SpecTec.null) (ht : SpecTec.heaptype)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Valtype_ok
        c (.RefT (.«% %» null ht))⟩)
      n (.success (.of ())) finalSupply ↔
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Heaptype_ok c ht⟩)
      n (.success (.of ())) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Valtype_ok:clause:0» c
            (.RefT (.«% %» null ht)))
          (fun _ => SpecTecExecution.tryClauses
            [SpecTec.«Valtype_ok:clause:1» c
              (.RefT (.«% %» null ht)),
              SpecTec.«Valtype_ok:clause:2» c
              (.RefT (.«% %» null ht))]))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«Valtype_ok:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond =>
            simp [SpecTec.«exec:match:valtype:NumT»] at hcond
      | orElse_unmatch hfailedSupply htail =>
        restore_supply hfailedSupply at htail
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Valtype_ok:clause:1» c
              (.RefT (.«% %» null ht)))
            (fun _ => SpecTecExecution.tryClauses
              [SpecTec.«Valtype_ok:clause:2» c
                (.RefT (.«% %» null ht))]))
          n (.success (.of ())) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«Valtype_ok:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond =>
              simp [SpecTec.«exec:match:valtype:VecT»] at hcond
        | orElse_unmatch hfailedSupply hlast =>
          restore_supply hfailedSupply at hlast
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Valtype_ok:clause:2» c
                (.RefT (.«% %» null ht)))
              (fun _ => .unmatch))
            n (.success (.of ())) finalSupply at hlast
          cases hlast with
          | orElse_success hthird =>
            unfold SpecTec.«Valtype_ok:clause:2» at hthird
            cases hthird with
            | bind_success hguard htail =>
              cases hguard with
              | guard_true _ =>
                cases htail with
                | bind_success href hpure =>
                  cases hpure with
                  | pure =>
                    exact (reftype_success_iff c null ht n finalSupply).1 href
          | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  · intro hheap
    have href := (reftype_success_iff c null ht n finalSupply).2 hheap
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Valtype_ok_clauses c (.RefT (.«% %» null ht))))
      n (.success (.of ())) finalSupply
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«Valtype_ok:clause:0» c (.RefT (.«% %» null ht)))
        n .unmatch n
      unfold SpecTec.«Valtype_ok:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp [SpecTec.«exec:match:valtype:NumT»]
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Valtype_ok:clause:1» c (.RefT (.«% %» null ht)))
          n .unmatch n
        unfold SpecTec.«Valtype_ok:clause:1»
        apply SpecTecExecution.Eval.bind_unmatch
        apply SpecTecExecution.Eval.guard_false
        simp [SpecTec.«exec:match:valtype:VecT»]
      · apply SpecTecExecution.tryClauses_cons_success
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Valtype_ok:clause:2» c (.RefT (.«% %» null ht)))
          n (.success (.of ())) finalSupply
        unfold SpecTec.«Valtype_ok:clause:2»
        apply SpecTecExecution.Eval.bind_success
        · apply SpecTecExecution.Eval.guard_true
          rfl
        · apply SpecTecExecution.Eval.bind_success href
          exact SpecTecExecution.Eval.pure ()

def valtypeValid (c : SpecTec.context) : SpecTec.valtype → Bool
  | .NumT _ => true
  | .VecT _ => true
  | .RefT (.«% %» _ ht) => HeaptypeValidation.heaptypeValid c ht
  | .BotT => false

theorem valtype_bot_no_success (c : SpecTec.context)
    (n finalSupply : Nat) :
    ¬ SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Valtype_ok c .BotT⟩)
      n (.success (.of ())) finalSupply := by
  intro h
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (.orElse (SpecTec.«Valtype_ok:clause:0» c .BotT)
        (fun _ => SpecTecExecution.tryClauses
          [SpecTec.«Valtype_ok:clause:1» c .BotT,
            SpecTec.«Valtype_ok:clause:2» c .BotT]))
      n (.success (.of ())) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«Valtype_ok:clause:0» at hfirst
      cases hfirst with
      | bind_success hguard _ =>
        cases hguard with
        | guard_true hcond =>
          simp [SpecTec.«exec:match:valtype:NumT»] at hcond
    | orElse_unmatch hfailedSupply htail =>
      restore_supply hfailedSupply at htail
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Valtype_ok:clause:1» c .BotT)
          (fun _ => SpecTecExecution.tryClauses
            [SpecTec.«Valtype_ok:clause:2» c .BotT]))
        n (.success (.of ())) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«Valtype_ok:clause:1» at hsecond
        cases hsecond with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond =>
            simp [SpecTec.«exec:match:valtype:VecT»] at hcond
      | orElse_unmatch hfailedSupply hlast =>
        restore_supply hfailedSupply at hlast
        change SpecTecExecution.Eval SpecTec.Body
          (.orElse (SpecTec.«Valtype_ok:clause:2» c .BotT)
            (fun _ => .unmatch))
          n (.success (.of ())) finalSupply at hlast
        cases hlast with
        | orElse_success hthird =>
          unfold SpecTec.«Valtype_ok:clause:2» at hthird
          cases hthird with
          | bind_success hguard _ =>
            cases hguard with
            | guard_true hcond =>
              simp [SpecTec.«exec:match:valtype:RefT»] at hcond
        | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem valtype_success_iff_valid (c : SpecTec.context)
    (t : SpecTec.valtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Valtype_ok c t⟩)
      n (.success (.of ())) finalSupply ↔
    valtypeValid c t = true ∧ finalSupply = n := by
  cases t with
  | NumT nt =>
    constructor
    · intro h
      obtain ⟨_, hsupply⟩ :=
        properties.wasm_module_ok.Execution.eval_deterministic h
          (valtype_num_total c nt n)
      exact ⟨rfl, hsupply⟩
    · rintro ⟨_, rfl⟩
      exact valtype_num_total c nt finalSupply
  | VecT vt =>
    constructor
    · intro h
      obtain ⟨_, hsupply⟩ :=
        properties.wasm_module_ok.Execution.eval_deterministic h
          (valtype_vec_total c vt n)
      exact ⟨rfl, hsupply⟩
    · rintro ⟨_, rfl⟩
      exact valtype_vec_total c vt finalSupply
  | RefT rt =>
    cases rt with
    | «% %» null ht =>
      rw [valtype_ref_success_iff,
        HeaptypeValidation.heaptype_success_iff_valid]
      rfl
  | BotT =>
    constructor
    · intro h
      exact (valtype_bot_no_success c n finalSupply h).elim
    · rintro ⟨hfalse, _⟩
      cases hfalse

end properties.wasm_module_ok.ValtypeValidation
