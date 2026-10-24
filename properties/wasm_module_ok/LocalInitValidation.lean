import properties.wasm_module_ok.bundle.Helpers

set_option autoImplicit false

namespace properties.wasm_module_ok.LocalInitValidation

theorem local_lookup_success_iff
    (c : SpecTec.context) (x : SpecTec.localidx)
    (lt : SpecTec.localtype) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.localtype, SpecTec.SpecTecCall.«$local» c x⟩)
      n (.success (.of lt)) finalSupply ↔
    c.LOCALS[x]? = some lt ∧ finalSupply = n := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«$local:clause:0» c x)
          (fun _ => .unmatch))
        n (.success (.of lt)) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«$local:clause:0» at hclause
        cases hclause with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true _ =>
            cases hget : c.LOCALS[x]? with
            | none =>
              rw [hget] at htail
              cases htail
            | some result =>
              rw [hget] at htail
              cases htail with
              | pure => exact ⟨rfl, rfl⟩
      | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨hget, rfl⟩
    have hbound : x < c.LOCALS.length :=
      (List.getElem?_eq_some_iff.mp hget).1
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$local_clauses» c x) ())
      finalSupply (.success (.of lt)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$local:clause:0» c x)
      finalSupply (.success (.of lt)) finalSupply
    unfold SpecTec.«$local:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      exact hbound
    · rw [hget]
      exact SpecTecExecution.Eval.pure lt

theorem local_lookup_none (c : SpecTec.context)
    (x : SpecTec.localidx) (n : Nat)
    (hget : c.LOCALS[x]? = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.localtype, SpecTec.SpecTecCall.«$local» c x⟩)
      n .unmatch n := by
  have hbound : ¬ x < c.LOCALS.length := by
    have hle : c.LOCALS.length ≤ x :=
      List.getElem?_eq_none_iff.mp hget
    exact Nat.not_lt.mpr hle
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$local_clauses» c x) ())
    n .unmatch n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$local:clause:0» c x) n .unmatch n
    unfold SpecTec.«$local:clause:0»
    apply SpecTecExecution.Eval.bind_unmatch
    exact SpecTecExecution.Eval.guard_false hbound
  · exact SpecTecExecution.firstSuccess_nil () n

def initLocalResult (c : SpecTec.context)
    (x : SpecTec.localidx) : Option SpecTec.context :=
  match c.LOCALS[x]? with
  | none => none
  | some (.LocalT _ t) =>
      some { c with LOCALS := c.LOCALS.set x (.LocalT .Set t) }

theorem init_local_of_lookup (c : SpecTec.context)
    (x : SpecTec.localidx) (init : SpecTec.init)
    (t : SpecTec.valtype) (n : Nat)
    (hget : c.LOCALS[x]? = some (.LocalT init t)) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.«$init_local» c x⟩)
      n (.success (.of
        { c with LOCALS := c.LOCALS.set x (.LocalT .Set t) })) n := by
  have hbound : x < c.LOCALS.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$init_local_clauses» c x) ())
    n (.success (.of
      { c with LOCALS := c.LOCALS.set x (.LocalT .Set t) })) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$init_local:clause:0» c x)
    n (.success (.of
      { c with LOCALS := c.LOCALS.set x (.LocalT .Set t) })) n
  unfold SpecTec.«$init_local:clause:0»
  apply SpecTecExecution.Eval.bind_success
    ((local_lookup_success_iff c x (.LocalT init t) n n).2
      ⟨hget, rfl⟩)
  apply SpecTecExecution.Eval.bind_success
  · unfold SpecTecExecution.require
    exact SpecTecExecution.Eval.orElse_success
      (SpecTecExecution.Eval.guard_true hbound)
  · exact SpecTecExecution.Eval.pure
      { c with LOCALS := c.LOCALS.set x (.LocalT .Set t) }

theorem init_local_success_iff
    (c : SpecTec.context) (x : SpecTec.localidx)
    (result : SpecTec.context) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.«$init_local» c x⟩)
      n (.success (.of result)) finalSupply ↔
    initLocalResult c x = some result ∧ finalSupply = n := by
  constructor
  · intro h
    have hgiven := h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«$init_local:clause:0» c x)
          (fun _ => .unmatch))
        n (.success (.of result)) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«$init_local:clause:0» at hclause
        cases hclause with
        | bind_success hlookup htail =>
          rename_i middle lt
          obtain ⟨hget, hmiddle⟩ :=
            (local_lookup_success_iff c x lt n middle).1 hlookup
          cases lt with
          | LocalT init t =>
            have hcanonical := init_local_of_lookup c x init t n hget
            obtain ⟨hout, hsupply⟩ :=
              SpecTecExecution.eval_deterministic hdet hgiven hcanonical
            cases hout
            exact ⟨by simp [initLocalResult, hget], hsupply⟩
      | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨hresult, rfl⟩
    cases hget : c.LOCALS[x]? with
    | none => simp [initLocalResult, hget] at hresult
    | some lt =>
      cases lt with
      | LocalT init t =>
        simp [initLocalResult, hget] at hresult
        cases hresult
        exact init_local_of_lookup c x init t finalSupply hget

theorem init_local_none (c : SpecTec.context)
    (x : SpecTec.localidx) (n : Nat)
    (hresult : initLocalResult c x = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_local» c x⟩)
      n .unmatch n := by
  cases hget : c.LOCALS[x]? with
  | none =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$init_local_clauses» c x) ())
      n .unmatch n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$init_local:clause:0» c x) n .unmatch n
      unfold SpecTec.«$init_local:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      exact local_lookup_none c x n hget
    · exact SpecTecExecution.firstSuccess_nil () n
  | some lt =>
    cases lt with
    | LocalT init t =>
      simp [initLocalResult, hget] at hresult

theorem init_locals_nil_total (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c []⟩)
      n (.success (.of c)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$init_locals_clauses» c []) ())
    n (.success (.of c)) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$init_locals:clause:0» c [])
    n (.success (.of c)) n
  unfold SpecTec.«$init_locals:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · apply SpecTecExecution.Eval.guard_true
    rfl
  · exact SpecTecExecution.Eval.pure c

theorem init_locals_cons_success_iff
    (c : SpecTec.context) (x : SpecTec.localidx)
    (xs : List SpecTec.localidx)
    (result : SpecTec.context) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c (x :: xs)⟩)
      n (.success (.of result)) finalSupply ↔
    ∃ (c₁ : SpecTec.context) (middle : Nat),
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.«$init_local» c x⟩)
        n (.success (.of c₁)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.context,
          SpecTec.SpecTecCall.«$init_locals» c₁ xs⟩)
        middle (.success (.of result)) finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (.orElse (SpecTec.«$init_locals:clause:0» c (x :: xs))
          (fun _ => SpecTecExecution.firstSuccess
            [fun _ => SpecTec.«$init_locals:clause:1» c (x :: xs)] ()))
        n (.success (.of result)) finalSupply at hbody
      cases hbody with
      | orElse_success hfirst =>
        unfold SpecTec.«$init_locals:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard _ =>
          cases hguard with
          | guard_true hcond => simp at hcond
      | orElse_unmatch _ htail =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.orElse (SpecTec.«$init_locals:clause:1» c (x :: xs))
            (fun _ => .unmatch))
          n (.success (.of result)) finalSupply at htail
        cases htail with
        | orElse_success hsecond =>
          unfold SpecTec.«$init_locals:clause:1» at hsecond
          cases hsecond with
          | bind_success hguard htail =>
            cases hguard with
            | guard_true _ =>
              cases htail with
              | bind_success hhead htail =>
                rename_i middle c₁
                cases htail with
                | bind_success hrest hpure =>
                  cases hpure with
                  | pure => exact ⟨c₁, middle, hhead, hrest⟩
        | orElse_unmatch _ hnone => cases hnone
  · rintro ⟨c₁, middle, hhead, hrest⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$init_locals_clauses» c (x :: xs)) ())
      n (.success (.of result)) finalSupply
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$init_locals:clause:0» c (x :: xs))
        n .unmatch n
      unfold SpecTec.«$init_locals:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$init_locals:clause:1» c (x :: xs))
        n (.success (.of result)) finalSupply
      unfold SpecTec.«$init_locals:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · apply SpecTecExecution.Eval.guard_true
        rfl
      · apply SpecTecExecution.Eval.bind_success hhead
        apply SpecTecExecution.Eval.bind_success hrest
        exact SpecTecExecution.Eval.pure result

def initLocalsResult (c : SpecTec.context) :
    List SpecTec.localidx → Option SpecTec.context
  | [] => some c
  | x :: xs =>
      (initLocalResult c x).bind fun c₁ => initLocalsResult c₁ xs

theorem init_locals_success_iff_result
    (c : SpecTec.context) (xs : List SpecTec.localidx)
    (result : SpecTec.context) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c xs⟩)
      n (.success (.of result)) finalSupply ↔
    initLocalsResult c xs = some result ∧ finalSupply = n := by
  induction xs generalizing c result n finalSupply with
  | nil =>
    constructor
    · intro h
      have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
        intro request x y hp
        cases hp
      obtain ⟨hout, hsupply⟩ :=
        SpecTecExecution.eval_deterministic hdet h
          (init_locals_nil_total c n)
      cases hout
      exact ⟨rfl, hsupply⟩
    · rintro ⟨hresult, hsupply⟩
      simp [initLocalsResult] at hresult
      cases hresult
      cases hsupply
      exact init_locals_nil_total c n
  | cons x xs ih =>
    constructor
    · intro h
      obtain ⟨c₁, middle, hhead, htail⟩ :=
        (init_locals_cons_success_iff
          c x xs result n finalSupply).1 h
      obtain ⟨hheadResult, hmiddle⟩ :=
        (init_local_success_iff c x c₁ n middle).1 hhead
      obtain ⟨htailResult, hsupply⟩ :=
        (ih c₁ result middle finalSupply).1 htail
      cases hmiddle
      exact ⟨by simp [initLocalsResult, hheadResult, htailResult],
        hsupply⟩
    · rintro ⟨hresult, hsupply⟩
      cases hhead : initLocalResult c x with
      | none =>
        simp [initLocalsResult, hhead] at hresult
      | some c₁ =>
        have htail : initLocalsResult c₁ xs = some result := by
          simpa [initLocalsResult, hhead] using hresult
        apply (init_locals_cons_success_iff
          c x xs result n finalSupply).2
        exact ⟨c₁, n,
          (init_local_success_iff c x c₁ n n).2 ⟨hhead, rfl⟩,
          (ih c₁ result n finalSupply).2 ⟨htail, hsupply⟩⟩

theorem init_locals_none (c : SpecTec.context)
    (xs : List SpecTec.localidx) (n : Nat)
    (hresult : initLocalsResult c xs = none) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c xs⟩)
      n .unmatch n := by
  induction xs generalizing c with
  | nil => simp [initLocalsResult] at hresult
  | cons x xs ih =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$init_locals_clauses» c (x :: xs)) ())
      n .unmatch n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$init_locals:clause:0» c (x :: xs))
        n .unmatch n
      unfold SpecTec.«$init_locals:clause:0»
      apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      simp
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$init_locals:clause:1» c (x :: xs))
          n .unmatch n
        unfold SpecTec.«$init_locals:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · apply SpecTecExecution.Eval.guard_true
          rfl
        · cases hhead : initLocalResult c x with
          | none =>
            apply SpecTecExecution.Eval.bind_unmatch
            exact init_local_none c x n hhead
          | some c₁ =>
            have htail : initLocalsResult c₁ xs = none := by
              simpa [initLocalsResult, hhead] using hresult
            apply SpecTecExecution.Eval.bind_success
              ((init_local_success_iff c x c₁ n n).2
                ⟨hhead, rfl⟩)
            apply SpecTecExecution.Eval.bind_unmatch
            exact ih c₁ htail
      · exact SpecTecExecution.firstSuccess_nil () n

def initLocalsOutcome (c : SpecTec.context)
    (xs : List SpecTec.localidx) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match initLocalsResult c xs with
  | some result => .success (.of result)
  | none => .unmatch

theorem init_locals_total (c : SpecTec.context)
    (xs : List SpecTec.localidx) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c xs⟩)
      n (initLocalsOutcome c xs) n := by
  cases hresult : initLocalsResult c xs with
  | none =>
    simpa [initLocalsOutcome, hresult] using
      init_locals_none c xs n hresult
  | some result =>
    simpa [initLocalsOutcome, hresult] using
      (init_locals_success_iff_result c xs result n n).2
        ⟨hresult, rfl⟩

theorem init_locals_deterministic (c : SpecTec.context)
    (xs : List SpecTec.localidx) (n finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.«$init_locals» c xs⟩)
      n outcome finalSupply) :
    outcome = initLocalsOutcome c xs ∧ finalSupply = n := by
  have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
    intro request x y hp
    cases hp
  exact SpecTecExecution.eval_deterministic hdet h
    (init_locals_total c xs n)

end properties.wasm_module_ok.LocalInitValidation
