import properties.wasm_module_ok.MatchValtypeConditional

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchResulttypeConditional

def allMatched (valMatch : SpecTec.valtype → SpecTec.valtype → Bool) :
    SpecTec.resulttype → SpecTec.resulttype → Bool
  | [], [] => true
  | t₁ :: ts₁, t₂ :: ts₂ =>
      valMatch t₁ t₂ && allMatched valMatch ts₁ ts₂
  | _, _ => false

def matchResulttypeResult
    (valMatch : SpecTec.valtype → SpecTec.valtype → Bool)
    (ts₁ ts₂ : SpecTec.resulttype) : Bool :=
  decide (ts₂.length = ts₁.length) && allMatched valMatch ts₁ ts₂

theorem iter_nil_total (dts : List SpecTec.deftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0»
          dts [] []⟩)
      n (.success (.of ())) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_resulttype:case_1:iter:0_clauses»
        dts [] []) ())
    n (.success (.of ())) n
  apply SpecTecExecution.firstSuccess_cons_success
  exact SpecTecExecution.Eval.pure ()

theorem iter_cons_success_iff
    (dts : List SpecTec.deftype)
    (t₁ t₂ : SpecTec.valtype)
    (ts₁ ts₂ : List SpecTec.valtype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0»
          dts (t₁ :: ts₁) (t₂ :: ts₂)⟩)
      n (.success (.of ())) finish ↔
    ∃ middle : Nat,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_valtype» dts t₁ t₂⟩)
        n (.success (.of true)) middle ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0»
            dts ts₁ ts₂⟩)
        middle (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.firstSuccess_success_iff
          (SpecTec.«$match_resulttype:case_1:iter:0_clauses»
            dts (t₁ :: ts₁) (t₂ :: ts₂)) ()
          n (.of ()) finish).1 hbody
      unfold SpecTec.«$match_resulttype:case_1:iter:0_clauses» at hselected
      cases hselected with
      | here hfirst =>
        change SpecTecExecution.Eval SpecTec.specTecProgram
          (.unmatch) n (.success (.of ())) finish at hfirst
        cases hfirst
      | next _ hrest =>
        cases hrest with
        | here hsecond =>
          unfold SpecTec.«$match_resulttype:case_1:iter:0:clause:1» at hsecond
          cases hsecond with
          | bind_success hval htail =>
            rename_i middle matched
            cases htail with
            | bind_success hguard htail =>
              cases hguard with
              | guard_true htrue =>
                cases htrue
                cases htail with
                | bind_success hiter hpure =>
                  cases hpure
                  exact ⟨middle, hval, hiter⟩
        | next _ hnone => cases hnone
  · rintro ⟨middle, hval, hiter⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_resulttype:case_1:iter:0_clauses»
          dts (t₁ :: ts₁) (t₂ :: ts₂)) ())
      n (.success (.of ())) finish
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_resulttype:case_1:iter:0:clause:0»
          dts (t₁ :: ts₁) (t₂ :: ts₂)) n .unmatch n
      exact SpecTecExecution.Eval.unmatch
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
          dts (t₁ :: ts₁) (t₂ :: ts₂))
        n (.success (.of ())) finish
      unfold SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
      apply SpecTecExecution.Eval.bind_success hval
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success hiter
        exact SpecTecExecution.Eval.pure ()

theorem iter_success_iff_allMatched_of_valtype
    (dts : List SpecTec.deftype)
    (valMatch : SpecTec.valtype → SpecTec.valtype → Bool)
    (hval : ∀ a b n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_valtype» dts a b⟩)
        n (.success (.of (valMatch a b))) n)
    (ts₁ ts₂ : SpecTec.resulttype)
    (hlen : ts₁.length = ts₂.length)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0»
          dts ts₁ ts₂⟩)
      n (.success (.of ())) finish ↔
    allMatched valMatch ts₁ ts₂ = true ∧ finish = n := by
  induction ts₁ generalizing ts₂ n finish with
  | nil =>
    cases ts₂ with
    | nil =>
      constructor
      · intro h
        have hdet : SpecTecExecution.PrimitiveDeterministic
            SpecTec.specTecProgram := by
          intro request x y hp
          cases hp
        obtain ⟨_, hsupply⟩ :=
          SpecTecExecution.eval_deterministic hdet h
            (iter_nil_total dts n)
        exact ⟨rfl, hsupply⟩
      · rintro ⟨_, rfl⟩
        exact iter_nil_total dts finish
    | cons t₂ ts₂ =>
      simp at hlen
  | cons t₁ ts₁ ih =>
    cases ts₂ with
    | nil =>
      simp at hlen
    | cons t₂ ts₂ =>
      have hlenTail : ts₁.length = ts₂.length := by
        simpa using hlen
      constructor
      · intro h
        obtain ⟨middle, hhead, htail⟩ :=
          (iter_cons_success_iff dts t₁ t₂ ts₁ ts₂ n finish).1 h
        have hdet : SpecTecExecution.PrimitiveDeterministic
            SpecTec.specTecProgram := by
          intro request x y hp
          cases hp
        obtain ⟨hresult, hmiddle⟩ :=
          SpecTecExecution.eval_deterministic hdet hhead
            (hval t₁ t₂ n)
        have hvalid : valMatch t₁ t₂ = true := by
          cases hv : valMatch t₁ t₂ with
          | false => simp [hv] at hresult
          | true => rfl
        obtain ⟨hrest, hsupply⟩ :=
          (ih ts₂ hlenTail middle finish).1 htail
        subst middle
        exact ⟨by simp [allMatched, hvalid, hrest], hsupply⟩
      · rintro ⟨hall, rfl⟩
        have hparts : valMatch t₁ t₂ = true ∧
            allMatched valMatch ts₁ ts₂ = true := by
          simpa [allMatched] using hall
        apply (iter_cons_success_iff
          dts t₁ t₂ ts₁ ts₂ finish finish).2
        exact ⟨finish,
          by simpa [hparts.1] using hval t₁ t₂ finish,
          (ih ts₂ hlenTail finish finish).2 ⟨hparts.2, rfl⟩⟩

theorem match_resulttype_true_iff_iter
    (dts : List SpecTec.deftype)
    (ts₁ ts₂ : SpecTec.resulttype)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_resulttype» dts ts₁ ts₂⟩)
      n (.success (.of true)) finish ↔
    ts₂.length = ts₁.length ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Unit,
          SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0»
            dts ts₁ ts₂⟩)
        n (.success (.of ())) finish := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (SpecTecExecution.firstSuccess_success_iff
          (SpecTec.«$match_resulttype_clauses» dts ts₁ ts₂) ()
          n (.of true) finish).1 hbody
      unfold SpecTec.«$match_resulttype_clauses» at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«$match_resulttype:clause:0» at hfirst
        cases hfirst with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true hlen =>
            cases htail with
            | bind_success hiter hpure =>
              cases hpure
              exact ⟨hlen, hiter⟩
      | next _ hrest =>
        cases hrest with
        | here hsecond =>
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (.pure false) n (.success (.of true)) finish at hsecond
          cases hsecond
        | next _ hnone => cases hnone
  · rintro ⟨hlen, hiter⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_resulttype_clauses» dts ts₁ ts₂) ())
      n (.success (.of true)) finish
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_resulttype:clause:0» dts ts₁ ts₂)
      n (.success (.of true)) finish
    unfold SpecTec.«$match_resulttype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true hlen
    · apply SpecTecExecution.Eval.bind_success hiter
      exact SpecTecExecution.Eval.pure true

theorem iter_unmatch_of_false
    (dts : List SpecTec.deftype)
    (valMatch : SpecTec.valtype → SpecTec.valtype → Bool)
    (hval : ∀ a b n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_valtype» dts a b⟩)
        n (.success (.of (valMatch a b))) n)
    (ts₁ ts₂ : SpecTec.resulttype)
    (hlen : ts₁.length = ts₂.length)
    (hfalse : allMatched valMatch ts₁ ts₂ = false)
    (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«$match_resulttype:case_1:iter:0»
          dts ts₁ ts₂⟩)
      n .unmatch n := by
  induction ts₁ generalizing ts₂ n with
  | nil =>
    cases ts₂ with
    | nil => simp [allMatched] at hfalse
    | cons t₂ ts₂ => simp at hlen
  | cons t₁ ts₁ ih =>
    cases ts₂ with
    | nil => simp at hlen
    | cons t₂ ts₂ =>
      have hlenTail : ts₁.length = ts₂.length := by
        simpa using hlen
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$match_resulttype:case_1:iter:0_clauses»
            dts (t₁ :: ts₁) (t₂ :: ts₂)) ())
        n .unmatch n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_resulttype:case_1:iter:0:clause:0»
            dts (t₁ :: ts₁) (t₂ :: ts₂)) n .unmatch n
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
              dts (t₁ :: ts₁) (t₂ :: ts₂)) n .unmatch n
          unfold SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
          cases hv : valMatch t₁ t₂ with
          | false =>
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hval t₁ t₂ n)
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false (by decide)
          | true =>
            have htailFalse : allMatched valMatch ts₁ ts₂ = false := by
              simpa [allMatched, hv] using hfalse
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hval t₁ t₂ n)
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · exact SpecTecExecution.Eval.bind_unmatch
                (ih ts₂ hlenTail htailFalse n)
        · exact SpecTecExecution.firstSuccess_nil () n

theorem match_resulttype_total_of_valtype
    (dts : List SpecTec.deftype)
    (valMatch : SpecTec.valtype → SpecTec.valtype → Bool)
    (hval : ∀ a b n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_valtype» dts a b⟩)
        n (.success (.of (valMatch a b))) n)
    (ts₁ ts₂ : SpecTec.resulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_resulttype» dts ts₁ ts₂⟩)
      n (.success (.of
        (matchResulttypeResult valMatch ts₁ ts₂))) n := by
  by_cases hlen : ts₂.length = ts₁.length
  · cases hall : allMatched valMatch ts₁ ts₂ with
    | true =>
      have hresult : matchResulttypeResult valMatch ts₁ ts₂ = true := by
        simp [matchResulttypeResult, hlen, hall]
      rw [hresult]
      apply (match_resulttype_true_iff_iter dts ts₁ ts₂ n n).2
      exact ⟨hlen,
        (iter_success_iff_allMatched_of_valtype
          dts valMatch hval ts₁ ts₂ hlen.symm n n).2
          ⟨hall, rfl⟩⟩
    | false =>
      have hresult : matchResulttypeResult valMatch ts₁ ts₂ = false := by
        simp [matchResulttypeResult, hlen, hall]
      rw [hresult]
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$match_resulttype_clauses» dts ts₁ ts₂) ())
        n (.success (.of false)) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_resulttype:clause:0» dts ts₁ ts₂)
          n .unmatch n
        unfold SpecTec.«$match_resulttype:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hlen
        · exact SpecTecExecution.Eval.bind_unmatch
            (iter_unmatch_of_false
              dts valMatch hval ts₁ ts₂ hlen.symm hall n)
      · apply SpecTecExecution.firstSuccess_cons_success
        exact SpecTecExecution.Eval.pure false
  · have hresult : matchResulttypeResult valMatch ts₁ ts₂ = false := by
      simp [matchResulttypeResult, hlen]
    rw [hresult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_resulttype_clauses» dts ts₁ ts₂) ())
      n (.success (.of false)) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_resulttype:clause:0» dts ts₁ ts₂)
        n .unmatch n
      unfold SpecTec.«$match_resulttype:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false hlen)
    · apply SpecTecExecution.firstSuccess_cons_success
      exact SpecTecExecution.Eval.pure false

theorem match_resulttype_success_iff_of_valtype
    (dts : List SpecTec.deftype)
    (valMatch : SpecTec.valtype → SpecTec.valtype → Bool)
    (hval : ∀ a b n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_valtype» dts a b⟩)
        n (.success (.of (valMatch a b))) n)
    (ts₁ ts₂ : SpecTec.resulttype) (result : Bool)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_resulttype» dts ts₁ ts₂⟩)
      n (.success (.of result)) finish ↔
    result = matchResulttypeResult valMatch ts₁ ts₂ ∧
      finish = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic
        SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h
        (match_resulttype_total_of_valtype
          dts valMatch hval ts₁ ts₂ n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact match_resulttype_total_of_valtype
      dts valMatch hval ts₁ ts₂ finish

end properties.wasm_module_ok.MatchResulttypeConditional
