import properties.wasm_module_ok.MatchResulttypeConditional
import properties.wasm_module_ok.MatchValtypeLocal
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchResulttypeLocal

theorem iter_success_iff_allMatched_of_local_valtype
    (dts : List SpecTec.deftype)
    (valMatch : SpecTec.valtype → SpecTec.valtype → Bool)
    (ts₁ ts₂ : SpecTec.resulttype)
    (hlen : ts₁.length = ts₂.length)
    (n finish : Nat)
    (hval : ∀ a, a ∈ ts₁ → ∀ b, b ∈ ts₂ → ∀ supply,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts a b⟩)
        supply (.success (.of (valMatch a b))) supply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«$match_resulttype:case_1:iter:0» dts ts₁ ts₂⟩)
      n (.success (.of ())) finish ↔
    MatchResulttypeConditional.allMatched valMatch ts₁ ts₂ = true ∧
      finish = n := by
  induction ts₁ generalizing ts₂ n finish with
  | nil =>
    cases ts₂ with
    | nil =>
      constructor
      · intro h
        obtain ⟨_, hsupply⟩ :=
          properties.wasm_module_ok.Execution.eval_deterministic h
            (MatchResulttypeConditional.iter_nil_total dts n)
        exact ⟨rfl, hsupply⟩
      · rintro ⟨_, rfl⟩
        exact MatchResulttypeConditional.iter_nil_total dts finish
    | cons t₂ ts₂ => simp at hlen
  | cons t₁ ts₁ ih =>
    cases ts₂ with
    | nil => simp at hlen
    | cons t₂ ts₂ =>
      have hlenTail : ts₁.length = ts₂.length := by
        simpa using hlen
      have hhead := hval t₁ (List.mem_cons_self) t₂ (List.mem_cons_self)
      have htailVal : ∀ a, a ∈ ts₁ → ∀ b, b ∈ ts₂ → ∀ supply,
          SpecTecExecution.Eval SpecTec.Body
            (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts a b⟩)
            supply (.success (.of (valMatch a b))) supply := by
        intro a ha b hb supply
        exact hval a (List.mem_cons_of_mem _ ha)
          b (List.mem_cons_of_mem _ hb) supply
      constructor
      · intro h
        obtain ⟨middle, hfirst, hrest⟩ :=
          (MatchResulttypeConditional.iter_cons_success_iff
            dts t₁ t₂ ts₁ ts₂ n finish).1 h
        obtain ⟨hresult, hmiddle⟩ :=
          properties.wasm_module_ok.Execution.eval_deterministic hfirst (hhead n)
        have hvalid : valMatch t₁ t₂ = true := by
          cases hv : valMatch t₁ t₂ with
          | false => simp [hv] at hresult
          | true => rfl
        obtain ⟨htail, hsupply⟩ :=
          (ih ts₂ hlenTail middle finish htailVal).1 hrest
        subst middle
        exact ⟨by simp [MatchResulttypeConditional.allMatched,
          hvalid, htail], hsupply⟩
      · rintro ⟨hall, rfl⟩
        have hparts : valMatch t₁ t₂ = true ∧
            MatchResulttypeConditional.allMatched valMatch ts₁ ts₂ = true := by
          simpa [MatchResulttypeConditional.allMatched] using hall
        apply (MatchResulttypeConditional.iter_cons_success_iff
          dts t₁ t₂ ts₁ ts₂ finish finish).2
        exact ⟨finish,
          by simpa [hparts.1] using hhead finish,
          (ih ts₂ hlenTail finish finish htailVal).2 ⟨hparts.2, rfl⟩⟩

theorem iter_unmatch_of_false_local
    (dts : List SpecTec.deftype)
    (valMatch : SpecTec.valtype → SpecTec.valtype → Bool)
    (ts₁ ts₂ : SpecTec.resulttype)
    (hlen : ts₁.length = ts₂.length)
    (hfalse : MatchResulttypeConditional.allMatched valMatch ts₁ ts₂ = false)
    (n : Nat)
    (hval : ∀ a, a ∈ ts₁ → ∀ b, b ∈ ts₂ → ∀ supply,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts a b⟩)
        supply (.success (.of (valMatch a b))) supply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«$match_resulttype:case_1:iter:0» dts ts₁ ts₂⟩)
      n .unmatch n := by
  induction ts₁ generalizing ts₂ n with
  | nil =>
    cases ts₂ with
    | nil => simp [MatchResulttypeConditional.allMatched] at hfalse
    | cons t₂ ts₂ => simp at hlen
  | cons t₁ ts₁ ih =>
    cases ts₂ with
    | nil => simp at hlen
    | cons t₂ ts₂ =>
      have hlenTail : ts₁.length = ts₂.length := by
        simpa using hlen
      have hhead := hval t₁ (List.mem_cons_self) t₂ (List.mem_cons_self)
      have htailVal : ∀ a, a ∈ ts₁ → ∀ b, b ∈ ts₂ → ∀ supply,
          SpecTecExecution.Eval SpecTec.Body
            (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts a b⟩)
            supply (.success (.of (valMatch a b))) supply := by
        intro a ha b hb supply
        exact hval a (List.mem_cons_of_mem _ ha)
          b (List.mem_cons_of_mem _ hb) supply
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$match_resulttype:case_1:iter:0_clauses»
            dts (t₁ :: ts₁) (t₂ :: ts₂)))
        n .unmatch n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_resulttype:case_1:iter:0:clause:0»
            dts (t₁ :: ts₁) (t₂ :: ts₂)) n .unmatch n
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
              dts (t₁ :: ts₁) (t₂ :: ts₂)) n .unmatch n
          unfold SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
          cases hv : valMatch t₁ t₂ with
          | false =>
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hhead n)
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false (by decide)
          | true =>
            have htailFalse :
                MatchResulttypeConditional.allMatched valMatch ts₁ ts₂ = false := by
              simpa [MatchResulttypeConditional.allMatched, hv] using hfalse
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hhead n)
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · exact SpecTecExecution.Eval.bind_unmatch
                (ih ts₂ hlenTail htailFalse n htailVal)
        · exact SpecTecExecution.tryClauses_nil n

theorem match_resulttype_total_of_local_valtype
    (dts : List SpecTec.deftype)
    (valMatch : SpecTec.valtype → SpecTec.valtype → Bool)
    (ts₁ ts₂ : SpecTec.resulttype) (n : Nat)
    (hval : ∀ a, a ∈ ts₁ → ∀ b, b ∈ ts₂ → ∀ supply,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts a b⟩)
        supply (.success (.of (valMatch a b))) supply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_resulttype» dts ts₁ ts₂⟩)
      n (.success (.of
        (MatchResulttypeConditional.matchResulttypeResult
          valMatch ts₁ ts₂))) n := by
  by_cases hlen : ts₂.length = ts₁.length
  · cases hall : MatchResulttypeConditional.allMatched valMatch ts₁ ts₂ with
    | true =>
      have hresult : MatchResulttypeConditional.matchResulttypeResult
          valMatch ts₁ ts₂ = true := by
        simp [MatchResulttypeConditional.matchResulttypeResult, hlen, hall]
      rw [hresult]
      apply (MatchResulttypeConditional.match_resulttype_true_iff_iter
        dts ts₁ ts₂ n n).2
      exact ⟨hlen,
        (iter_success_iff_allMatched_of_local_valtype
          dts valMatch ts₁ ts₂ hlen.symm n n hval).2 ⟨hall, rfl⟩⟩
    | false =>
      have hresult : MatchResulttypeConditional.matchResulttypeResult
          valMatch ts₁ ts₂ = false := by
        simp [MatchResulttypeConditional.matchResulttypeResult, hlen, hall]
      rw [hresult]
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$match_resulttype_clauses» dts ts₁ ts₂))
        n (.success (.of false)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_resulttype:clause:0» dts ts₁ ts₂)
          n .unmatch n
        unfold SpecTec.«$match_resulttype:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hlen
        · exact SpecTecExecution.Eval.bind_unmatch
            (iter_unmatch_of_false_local
              dts valMatch ts₁ ts₂ hlen.symm hall n hval)
      · apply SpecTecExecution.tryClauses_cons_success
        exact SpecTecExecution.Eval.pure false
  · have hresult : MatchResulttypeConditional.matchResulttypeResult
        valMatch ts₁ ts₂ = false := by
      simp [MatchResulttypeConditional.matchResulttypeResult, hlen]
    rw [hresult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_resulttype_clauses» dts ts₁ ts₂))
      n (.success (.of false)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_resulttype:clause:0» dts ts₁ ts₂)
        n .unmatch n
      unfold SpecTec.«$match_resulttype:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false hlen)
    · apply SpecTecExecution.tryClauses_cons_success
      exact SpecTecExecution.Eval.pure false

theorem match_resulttype_total_of_local_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (ts₁ ts₂ : SpecTec.resulttype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ts₁.flatMap ReadyMatchReachability.sourceValHeaptypes →
      h2 ∈ ts₂.flatMap ReadyMatchReachability.sourceValHeaptypes →
      ∀ supply, SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_resulttype» dts ts₁ ts₂⟩)
      n (.success (.of
        (MatchResulttypeConditional.matchResulttypeResult
          (MatchValtypeConditional.matchValtypeResult heapMatch)
          ts₁ ts₂))) n := by
  apply match_resulttype_total_of_local_valtype
  intro a ha b hb supply
  apply MatchValtypeLocal.match_valtype_total_of_local_heap
  intro h1 h2 hm1 hm2 s
  apply hheap h1 h2
  · exact List.mem_flatMap.mpr ⟨a, ha, hm1⟩
  · exact List.mem_flatMap.mpr ⟨b, hb, hm2⟩

theorem iter_success_iff_allMatched_of_local_valtype_at
    (dts : List SpecTec.deftype)
    (valMatch : SpecTec.valtype → SpecTec.valtype → Bool)
    (ts₁ ts₂ : SpecTec.resulttype)
    (hlen : ts₁.length = ts₂.length)
    (n finish : Nat)
    (hval : ∀ a, a ∈ ts₁ → ∀ b, b ∈ ts₂ →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts a b⟩)
        n (.success (.of (valMatch a b))) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«$match_resulttype:case_1:iter:0» dts ts₁ ts₂⟩)
      n (.success (.of ())) finish ↔
    MatchResulttypeConditional.allMatched valMatch ts₁ ts₂ = true ∧
      finish = n := by
  induction ts₁ generalizing ts₂ n finish with
  | nil =>
    cases ts₂ with
    | nil =>
      constructor
      · intro h
        obtain ⟨_, hsupply⟩ :=
          properties.wasm_module_ok.Execution.eval_deterministic h
            (MatchResulttypeConditional.iter_nil_total dts n)
        exact ⟨rfl, hsupply⟩
      · rintro ⟨_, rfl⟩
        exact MatchResulttypeConditional.iter_nil_total dts finish
    | cons t₂ ts₂ => simp at hlen
  | cons t₁ ts₁ ih =>
    cases ts₂ with
    | nil => simp at hlen
    | cons t₂ ts₂ =>
      have hlenTail : ts₁.length = ts₂.length := by
        simpa using hlen
      have hhead := hval t₁ (List.mem_cons_self) t₂ (List.mem_cons_self)
      have htailVal : ∀ a, a ∈ ts₁ → ∀ b, b ∈ ts₂ →
          SpecTecExecution.Eval SpecTec.Body
            (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts a b⟩)
            n (.success (.of (valMatch a b))) n := by
        intro a ha b hb
        exact hval a (List.mem_cons_of_mem _ ha)
          b (List.mem_cons_of_mem _ hb)
      constructor
      · intro h
        obtain ⟨middle, hfirst, hrest⟩ :=
          (MatchResulttypeConditional.iter_cons_success_iff
            dts t₁ t₂ ts₁ ts₂ n finish).1 h
        obtain ⟨hresult, hmiddle⟩ :=
          properties.wasm_module_ok.Execution.eval_deterministic hfirst hhead
        have hvalid : valMatch t₁ t₂ = true := by
          cases hv : valMatch t₁ t₂ with
          | false => simp [hv] at hresult
          | true => rfl
        obtain ⟨htail, hsupply⟩ :=
          (ih ts₂ hlenTail n finish htailVal).1 (by
            subst middle
            exact hrest)
        exact ⟨by simp [MatchResulttypeConditional.allMatched,
          hvalid, htail], hsupply⟩
      · rintro ⟨hall, rfl⟩
        have hparts : valMatch t₁ t₂ = true ∧
            MatchResulttypeConditional.allMatched valMatch ts₁ ts₂ = true := by
          simpa [MatchResulttypeConditional.allMatched] using hall
        apply (MatchResulttypeConditional.iter_cons_success_iff
          dts t₁ t₂ ts₁ ts₂ finish finish).2
        exact ⟨finish,
          by simpa [hparts.1] using hhead,
          (ih ts₂ hlenTail finish finish htailVal).2 ⟨hparts.2, rfl⟩⟩

theorem iter_unmatch_of_false_local_at
    (dts : List SpecTec.deftype)
    (valMatch : SpecTec.valtype → SpecTec.valtype → Bool)
    (ts₁ ts₂ : SpecTec.resulttype)
    (hlen : ts₁.length = ts₂.length)
    (hfalse : MatchResulttypeConditional.allMatched valMatch ts₁ ts₂ = false)
    (n : Nat)
    (hval : ∀ a, a ∈ ts₁ → ∀ b, b ∈ ts₂ →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts a b⟩)
        n (.success (.of (valMatch a b))) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«$match_resulttype:case_1:iter:0» dts ts₁ ts₂⟩)
      n .unmatch n := by
  induction ts₁ generalizing ts₂ n with
  | nil =>
    cases ts₂ with
    | nil => simp [MatchResulttypeConditional.allMatched] at hfalse
    | cons t₂ ts₂ => simp at hlen
  | cons t₁ ts₁ ih =>
    cases ts₂ with
    | nil => simp at hlen
    | cons t₂ ts₂ =>
      have hlenTail : ts₁.length = ts₂.length := by
        simpa using hlen
      have hhead := hval t₁ (List.mem_cons_self) t₂ (List.mem_cons_self)
      have htailVal : ∀ a, a ∈ ts₁ → ∀ b, b ∈ ts₂ →
          SpecTecExecution.Eval SpecTec.Body
            (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts a b⟩)
            n (.success (.of (valMatch a b))) n := by
        intro a ha b hb
        exact hval a (List.mem_cons_of_mem _ ha)
          b (List.mem_cons_of_mem _ hb)
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$match_resulttype:case_1:iter:0_clauses»
            dts (t₁ :: ts₁) (t₂ :: ts₂)))
        n .unmatch n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_resulttype:case_1:iter:0:clause:0»
            dts (t₁ :: ts₁) (t₂ :: ts₂)) n .unmatch n
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
              dts (t₁ :: ts₁) (t₂ :: ts₂)) n .unmatch n
          unfold SpecTec.«$match_resulttype:case_1:iter:0:clause:1»
          cases hv : valMatch t₁ t₂ with
          | false =>
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hhead)
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false (by decide)
          | true =>
            have htailFalse :
                MatchResulttypeConditional.allMatched valMatch ts₁ ts₂ = false := by
              simpa [MatchResulttypeConditional.allMatched, hv] using hfalse
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hhead)
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · exact SpecTecExecution.Eval.bind_unmatch
                (ih ts₂ hlenTail htailFalse n htailVal)
        · exact SpecTecExecution.tryClauses_nil n

theorem match_resulttype_total_of_local_valtype_at
    (dts : List SpecTec.deftype)
    (valMatch : SpecTec.valtype → SpecTec.valtype → Bool)
    (ts₁ ts₂ : SpecTec.resulttype) (n : Nat)
    (hval : ∀ a, a ∈ ts₁ → ∀ b, b ∈ ts₂ →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts a b⟩)
        n (.success (.of (valMatch a b))) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_resulttype» dts ts₁ ts₂⟩)
      n (.success (.of
        (MatchResulttypeConditional.matchResulttypeResult
          valMatch ts₁ ts₂))) n := by
  by_cases hlen : ts₂.length = ts₁.length
  · cases hall : MatchResulttypeConditional.allMatched valMatch ts₁ ts₂ with
    | true =>
      have hresult : MatchResulttypeConditional.matchResulttypeResult
          valMatch ts₁ ts₂ = true := by
        simp [MatchResulttypeConditional.matchResulttypeResult, hlen, hall]
      rw [hresult]
      apply (MatchResulttypeConditional.match_resulttype_true_iff_iter
        dts ts₁ ts₂ n n).2
      exact ⟨hlen,
        (iter_success_iff_allMatched_of_local_valtype_at
          dts valMatch ts₁ ts₂ hlen.symm n n hval).2 ⟨hall, rfl⟩⟩
    | false =>
      have hresult : MatchResulttypeConditional.matchResulttypeResult
          valMatch ts₁ ts₂ = false := by
        simp [MatchResulttypeConditional.matchResulttypeResult, hlen, hall]
      rw [hresult]
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$match_resulttype_clauses» dts ts₁ ts₂))
        n (.success (.of false)) n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_resulttype:clause:0» dts ts₁ ts₂)
          n .unmatch n
        unfold SpecTec.«$match_resulttype:clause:0»
        apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hlen
        · exact SpecTecExecution.Eval.bind_unmatch
            (iter_unmatch_of_false_local_at
              dts valMatch ts₁ ts₂ hlen.symm hall n hval)
      · apply SpecTecExecution.tryClauses_cons_success
        exact SpecTecExecution.Eval.pure false
  · have hresult : MatchResulttypeConditional.matchResulttypeResult
        valMatch ts₁ ts₂ = false := by
      simp [MatchResulttypeConditional.matchResulttypeResult, hlen]
    rw [hresult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_resulttype_clauses» dts ts₁ ts₂))
      n (.success (.of false)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_resulttype:clause:0» dts ts₁ ts₂)
        n .unmatch n
      unfold SpecTec.«$match_resulttype:clause:0»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false hlen)
    · apply SpecTecExecution.tryClauses_cons_success
      exact SpecTecExecution.Eval.pure false

theorem match_resulttype_total_of_local_heap_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (ts₁ ts₂ : SpecTec.resulttype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ts₁.flatMap ReadyMatchReachability.sourceValHeaptypes →
      h2 ∈ ts₂.flatMap ReadyMatchReachability.sourceValHeaptypes →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_resulttype» dts ts₁ ts₂⟩)
      n (.success (.of
        (MatchResulttypeConditional.matchResulttypeResult
          (MatchValtypeConditional.matchValtypeResult heapMatch)
          ts₁ ts₂))) n := by
  apply match_resulttype_total_of_local_valtype_at
  intro a ha b hb
  apply MatchValtypeLocal.match_valtype_total_of_local_heap_at
  intro h1 h2 hm1 hm2
  apply hheap h1 h2
  · exact List.mem_flatMap.mpr ⟨a, ha, hm1⟩
  · exact List.mem_flatMap.mpr ⟨b, hb, hm2⟩

end properties.wasm_module_ok.MatchResulttypeLocal
