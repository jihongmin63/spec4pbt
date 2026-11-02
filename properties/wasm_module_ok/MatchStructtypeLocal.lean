import properties.wasm_module_ok.MatchStructtypeConditional
import properties.wasm_module_ok.MatchFieldLocal
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchStructtypeLocal

theorem iter_success_iff_allFieldsMatched_of_local_field
    (dts : List SpecTec.deftype)
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool)
    (as bs : List SpecTec.fieldtype)
    (hlen : as.length = bs.length)
    (n finish : Nat)
    (hfield : ∀ a, a ∈ as → ∀ b, b ∈ bs → ∀ supply,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a b⟩)
        supply (.success (.of (fieldMatch a b))) supply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«$match_structtype:case_1:iter:0» dts as bs⟩)
      n (.success (.of ())) finish ↔
    MatchStructtypeConditional.allFieldsMatched fieldMatch as bs = true ∧
      finish = n := by
  induction as generalizing bs n finish with
  | nil =>
    cases bs with
    | nil =>
      constructor
      · intro h
        obtain ⟨_, hsupply⟩ :=
          properties.wasm_module_ok.Execution.eval_deterministic h
            (MatchStructtypeConditional.iter_nil_total dts n)
        exact ⟨rfl, hsupply⟩
      · rintro ⟨_, rfl⟩
        exact MatchStructtypeConditional.iter_nil_total dts finish
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlenTail : as.length = bs.length := by
        simpa using hlen
      have hhead := hfield a (List.mem_cons_self) b (List.mem_cons_self)
      have htailField : ∀ a', a' ∈ as → ∀ b', b' ∈ bs → ∀ supply,
          SpecTecExecution.Eval SpecTec.Body
            (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a' b'⟩)
            supply (.success (.of (fieldMatch a' b'))) supply := by
        intro a' ha b' hb supply
        exact hfield a' (List.mem_cons_of_mem _ ha)
          b' (List.mem_cons_of_mem _ hb) supply
      constructor
      · intro h
        obtain ⟨middle, hfirst, hrest⟩ :=
          (MatchStructtypeConditional.iter_cons_success_iff
            dts a b as bs n finish).1 h
        obtain ⟨hresult, hmiddle⟩ :=
          properties.wasm_module_ok.Execution.eval_deterministic hfirst (hhead n)
        have hvalid : fieldMatch a b = true := by
          cases hv : fieldMatch a b with
          | false => simp [hv] at hresult
          | true => rfl
        obtain ⟨htail, hsupply⟩ :=
          (ih bs hlenTail middle finish htailField).1 hrest
        subst middle
        exact ⟨by simp [MatchStructtypeConditional.allFieldsMatched,
          hvalid, htail], hsupply⟩
      · rintro ⟨hall, rfl⟩
        have hparts : fieldMatch a b = true ∧
            MatchStructtypeConditional.allFieldsMatched fieldMatch as bs = true := by
          simpa [MatchStructtypeConditional.allFieldsMatched] using hall
        apply (MatchStructtypeConditional.iter_cons_success_iff
          dts a b as bs finish finish).2
        exact ⟨finish,
          by simpa [hparts.1] using hhead finish,
          (ih bs hlenTail finish finish htailField).2 ⟨hparts.2, rfl⟩⟩

theorem iter_unmatch_of_false_local
    (dts : List SpecTec.deftype)
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool)
    (as bs : List SpecTec.fieldtype)
    (hlen : as.length = bs.length)
    (hfalse : MatchStructtypeConditional.allFieldsMatched fieldMatch as bs = false)
    (n : Nat)
    (hfield : ∀ a, a ∈ as → ∀ b, b ∈ bs → ∀ supply,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a b⟩)
        supply (.success (.of (fieldMatch a b))) supply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«$match_structtype:case_1:iter:0» dts as bs⟩)
      n .unmatch n := by
  induction as generalizing bs n with
  | nil =>
    cases bs with
    | nil => simp [MatchStructtypeConditional.allFieldsMatched] at hfalse
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlenTail : as.length = bs.length := by
        simpa using hlen
      have hhead := hfield a (List.mem_cons_self) b (List.mem_cons_self)
      have htailField : ∀ a', a' ∈ as → ∀ b', b' ∈ bs → ∀ supply,
          SpecTecExecution.Eval SpecTec.Body
            (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a' b'⟩)
            supply (.success (.of (fieldMatch a' b'))) supply := by
        intro a' ha b' hb supply
        exact hfield a' (List.mem_cons_of_mem _ ha)
          b' (List.mem_cons_of_mem _ hb) supply
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$match_structtype:case_1:iter:0_clauses»
            dts (a :: as) (b :: bs)))
        n .unmatch n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_structtype:case_1:iter:0:clause:0»
            dts (a :: as) (b :: bs)) n .unmatch n
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$match_structtype:case_1:iter:0:clause:1»
              dts (a :: as) (b :: bs)) n .unmatch n
          unfold SpecTec.«$match_structtype:case_1:iter:0:clause:1»
          cases hv : fieldMatch a b with
          | false =>
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hhead n)
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false (by decide)
          | true =>
            have htailFalse :
                MatchStructtypeConditional.allFieldsMatched fieldMatch as bs = false := by
              simpa [MatchStructtypeConditional.allFieldsMatched, hv] using hfalse
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hhead n)
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · exact SpecTecExecution.Eval.bind_unmatch
                (ih bs hlenTail htailFalse n htailField)
        · exact SpecTecExecution.tryClauses_nil n

theorem match_structtype_total_of_local_field
    (dts : List SpecTec.deftype)
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool)
    (as bs : List SpecTec.fieldtype) (n : Nat)
    (hfield : ∀ a, a ∈ as → ∀ b, b ∈ bs → ∀ supply,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a b⟩)
        supply (.success (.of (fieldMatch a b))) supply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_structtype»
          dts (.StructT as) (.StructT bs)⟩)
      n (.success (.of
        (MatchStructtypeConditional.structMatch fieldMatch
          (.StructT as) (.StructT bs)))) n := by
  by_cases hwidth : bs.length ≤ as.length
  · have hlen : (as.take bs.length).length = bs.length := by
      simp [List.length_take, Nat.min_eq_left hwidth]
    have hprefixField : ∀ a, a ∈ as.take bs.length →
        ∀ b, b ∈ bs → ∀ supply,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a b⟩)
          supply (.success (.of (fieldMatch a b))) supply := by
      intro a ha b hb supply
      exact hfield a (List.mem_of_mem_take ha) b hb supply
    cases hall : MatchStructtypeConditional.allFieldsMatched
        fieldMatch (as.take bs.length) bs with
    | true =>
      have hresult : MatchStructtypeConditional.structMatch
          fieldMatch (.StructT as) (.StructT bs) = true := by
        simp [MatchStructtypeConditional.structMatch, hwidth, hall]
      rw [hresult]
      apply MatchStructtypeConditional.match_structtype_true_of_iter
        dts as bs hwidth n n
      exact (iter_success_iff_allFieldsMatched_of_local_field
        dts fieldMatch (as.take bs.length) bs hlen n n hprefixField).2
          ⟨hall, rfl⟩
    | false =>
      have hresult : MatchStructtypeConditional.structMatch
          fieldMatch (.StructT as) (.StructT bs) = false := by
        simp [MatchStructtypeConditional.structMatch, hwidth, hall]
      rw [hresult]
      exact MatchStructtypeConditional.match_structtype_false_of_iter_unmatch
        dts as bs hwidth n
        (iter_unmatch_of_false_local dts fieldMatch
          (as.take bs.length) bs hlen hall n hprefixField)
  · have hresult : MatchStructtypeConditional.structMatch
        fieldMatch (.StructT as) (.StructT bs) = false := by
      simp [MatchStructtypeConditional.structMatch, hwidth]
    rw [hresult]
    exact MatchStructtypeConditional.match_structtype_false_of_width_fail
      dts as bs hwidth n

theorem match_structtype_total_of_local_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.structtype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT a) →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT b) →
      ∀ supply, SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT b) →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT a) →
      ∀ supply, SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h2 h1⟩)
        supply (.success (.of (heapMatch h2 h1))) supply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_structtype» dts a b⟩)
      n (.success (.of
        (MatchStructtypeConditional.structMatch
          (MatchFieldConditional.fieldMatch heapMatch) a b))) n := by
  cases a with
  | StructT as =>
    cases b with
    | StructT bs =>
      apply match_structtype_total_of_local_field
      intro fieldA hfieldA fieldB hfieldB supply
      apply MatchFieldLocal.match_field_total_of_local_heap
      · intro h1 h2 hm1 hm2 s
        apply hheap h1 h2
        · change h1 ∈ as.flatMap ReadyMatchReachability.sourceFieldHeaptypes
          exact List.mem_flatMap.mpr ⟨fieldA, hfieldA, hm1⟩
        · change h2 ∈ bs.flatMap ReadyMatchReachability.sourceFieldHeaptypes
          exact List.mem_flatMap.mpr ⟨fieldB, hfieldB, hm2⟩
      · intro h2 h1 hm2 hm1 s
        apply hheapReverse h2 h1
        · change h2 ∈ bs.flatMap ReadyMatchReachability.sourceFieldHeaptypes
          exact List.mem_flatMap.mpr ⟨fieldB, hfieldB, hm2⟩
        · change h1 ∈ as.flatMap ReadyMatchReachability.sourceFieldHeaptypes
          exact List.mem_flatMap.mpr ⟨fieldA, hfieldA, hm1⟩

theorem iter_success_iff_allFieldsMatched_of_local_field_at
    (dts : List SpecTec.deftype)
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool)
    (as bs : List SpecTec.fieldtype)
    (hlen : as.length = bs.length)
    (n finish : Nat)
    (hfield : ∀ a, a ∈ as → ∀ b, b ∈ bs →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a b⟩)
        n (.success (.of (fieldMatch a b))) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«$match_structtype:case_1:iter:0» dts as bs⟩)
      n (.success (.of ())) finish ↔
    MatchStructtypeConditional.allFieldsMatched fieldMatch as bs = true ∧
      finish = n := by
  induction as generalizing bs n finish with
  | nil =>
    cases bs with
    | nil =>
      constructor
      · intro h
        obtain ⟨_, hsupply⟩ :=
          properties.wasm_module_ok.Execution.eval_deterministic h
            (MatchStructtypeConditional.iter_nil_total dts n)
        exact ⟨rfl, hsupply⟩
      · rintro ⟨_, rfl⟩
        exact MatchStructtypeConditional.iter_nil_total dts finish
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlenTail : as.length = bs.length := by
        simpa using hlen
      have hhead := hfield a (List.mem_cons_self) b (List.mem_cons_self)
      have htailField : ∀ a', a' ∈ as → ∀ b', b' ∈ bs →
          SpecTecExecution.Eval SpecTec.Body
            (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a' b'⟩)
            n (.success (.of (fieldMatch a' b'))) n := by
        intro a' ha b' hb
        exact hfield a' (List.mem_cons_of_mem _ ha)
          b' (List.mem_cons_of_mem _ hb)
      constructor
      · intro h
        obtain ⟨middle, hfirst, hrest⟩ :=
          (MatchStructtypeConditional.iter_cons_success_iff
            dts a b as bs n finish).1 h
        obtain ⟨hresult, hmiddle⟩ :=
          properties.wasm_module_ok.Execution.eval_deterministic hfirst hhead
        have hvalid : fieldMatch a b = true := by
          cases hv : fieldMatch a b with
          | false => simp [hv] at hresult
          | true => rfl
        obtain ⟨htail, hsupply⟩ :=
          (ih bs hlenTail n finish htailField).1 (by
            subst middle
            exact hrest)
        exact ⟨by simp [MatchStructtypeConditional.allFieldsMatched,
          hvalid, htail], hsupply⟩
      · rintro ⟨hall, rfl⟩
        have hparts : fieldMatch a b = true ∧
            MatchStructtypeConditional.allFieldsMatched fieldMatch as bs = true := by
          simpa [MatchStructtypeConditional.allFieldsMatched] using hall
        apply (MatchStructtypeConditional.iter_cons_success_iff
          dts a b as bs finish finish).2
        exact ⟨finish,
          by simpa [hparts.1] using hhead,
          (ih bs hlenTail finish finish htailField).2 ⟨hparts.2, rfl⟩⟩

theorem iter_unmatch_of_false_local_at
    (dts : List SpecTec.deftype)
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool)
    (as bs : List SpecTec.fieldtype)
    (hlen : as.length = bs.length)
    (hfalse : MatchStructtypeConditional.allFieldsMatched fieldMatch as bs = false)
    (n : Nat)
    (hfield : ∀ a, a ∈ as → ∀ b, b ∈ bs →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a b⟩)
        n (.success (.of (fieldMatch a b))) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«$match_structtype:case_1:iter:0» dts as bs⟩)
      n .unmatch n := by
  induction as generalizing bs n with
  | nil =>
    cases bs with
    | nil => simp [MatchStructtypeConditional.allFieldsMatched] at hfalse
    | cons b bs => simp at hlen
  | cons a as ih =>
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have hlenTail : as.length = bs.length := by
        simpa using hlen
      have hhead := hfield a (List.mem_cons_self) b (List.mem_cons_self)
      have htailField : ∀ a', a' ∈ as → ∀ b', b' ∈ bs →
          SpecTecExecution.Eval SpecTec.Body
            (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a' b'⟩)
            n (.success (.of (fieldMatch a' b'))) n := by
        intro a' ha b' hb
        exact hfield a' (List.mem_cons_of_mem _ ha)
          b' (List.mem_cons_of_mem _ hb)
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$match_structtype:case_1:iter:0_clauses»
            dts (a :: as) (b :: bs)))
        n .unmatch n
      apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_structtype:case_1:iter:0:clause:0»
            dts (a :: as) (b :: bs)) n .unmatch n
        exact SpecTecExecution.Eval.unmatch
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.Body
            (SpecTec.«$match_structtype:case_1:iter:0:clause:1»
              dts (a :: as) (b :: bs)) n .unmatch n
          unfold SpecTec.«$match_structtype:case_1:iter:0:clause:1»
          cases hv : fieldMatch a b with
          | false =>
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hhead)
            apply SpecTecExecution.Eval.bind_unmatch
            exact SpecTecExecution.Eval.guard_false (by decide)
          | true =>
            have htailFalse :
                MatchStructtypeConditional.allFieldsMatched fieldMatch as bs = false := by
              simpa [MatchStructtypeConditional.allFieldsMatched, hv] using hfalse
            apply SpecTecExecution.Eval.bind_success
              (by simpa [hv] using hhead)
            apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · exact SpecTecExecution.Eval.bind_unmatch
                (ih bs hlenTail htailFalse n htailField)
        · exact SpecTecExecution.tryClauses_nil n

theorem match_structtype_total_of_local_field_at
    (dts : List SpecTec.deftype)
    (fieldMatch : SpecTec.fieldtype → SpecTec.fieldtype → Bool)
    (as bs : List SpecTec.fieldtype) (n : Nat)
    (hfield : ∀ a, a ∈ as → ∀ b, b ∈ bs →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a b⟩)
        n (.success (.of (fieldMatch a b))) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_structtype»
          dts (.StructT as) (.StructT bs)⟩)
      n (.success (.of
        (MatchStructtypeConditional.structMatch fieldMatch
          (.StructT as) (.StructT bs)))) n := by
  by_cases hwidth : bs.length ≤ as.length
  · have hlen : (as.take bs.length).length = bs.length := by
      simp [List.length_take, Nat.min_eq_left hwidth]
    have hprefixField : ∀ a, a ∈ as.take bs.length →
        ∀ b, b ∈ bs →
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a b⟩)
          n (.success (.of (fieldMatch a b))) n := by
      intro a ha b hb
      exact hfield a (List.mem_of_mem_take ha) b hb
    cases hall : MatchStructtypeConditional.allFieldsMatched
        fieldMatch (as.take bs.length) bs with
    | true =>
      have hresult : MatchStructtypeConditional.structMatch
          fieldMatch (.StructT as) (.StructT bs) = true := by
        simp [MatchStructtypeConditional.structMatch, hwidth, hall]
      rw [hresult]
      apply MatchStructtypeConditional.match_structtype_true_of_iter
        dts as bs hwidth n n
      exact (iter_success_iff_allFieldsMatched_of_local_field_at
        dts fieldMatch (as.take bs.length) bs hlen n n hprefixField).2
          ⟨hall, rfl⟩
    | false =>
      have hresult : MatchStructtypeConditional.structMatch
          fieldMatch (.StructT as) (.StructT bs) = false := by
        simp [MatchStructtypeConditional.structMatch, hwidth, hall]
      rw [hresult]
      exact MatchStructtypeConditional.match_structtype_false_of_iter_unmatch
        dts as bs hwidth n
        (iter_unmatch_of_false_local_at dts fieldMatch
          (as.take bs.length) bs hlen hall n hprefixField)
  · have hresult : MatchStructtypeConditional.structMatch
        fieldMatch (.StructT as) (.StructT bs) = false := by
      simp [MatchStructtypeConditional.structMatch, hwidth]
    rw [hresult]
    exact MatchStructtypeConditional.match_structtype_false_of_width_fail
      dts as bs hwidth n

theorem match_structtype_total_of_local_heap_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.structtype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT a) →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT b) →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT b) →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT a) →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h2 h1⟩)
        n (.success (.of (heapMatch h2 h1))) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_structtype» dts a b⟩)
      n (.success (.of
        (MatchStructtypeConditional.structMatch
          (MatchFieldConditional.fieldMatch heapMatch) a b))) n := by
  cases a with
  | StructT as =>
    cases b with
    | StructT bs =>
      apply match_structtype_total_of_local_field_at
      intro fieldA hfieldA fieldB hfieldB
      apply MatchFieldLocal.match_field_total_of_local_heap_at
      · intro h1 h2 hm1 hm2
        apply hheap h1 h2
        · change h1 ∈ as.flatMap ReadyMatchReachability.sourceFieldHeaptypes
          exact List.mem_flatMap.mpr ⟨fieldA, hfieldA, hm1⟩
        · change h2 ∈ bs.flatMap ReadyMatchReachability.sourceFieldHeaptypes
          exact List.mem_flatMap.mpr ⟨fieldB, hfieldB, hm2⟩
      · intro h2 h1 hm2 hm1
        apply hheapReverse h2 h1
        · change h2 ∈ bs.flatMap ReadyMatchReachability.sourceFieldHeaptypes
          exact List.mem_flatMap.mpr ⟨fieldB, hfieldB, hm2⟩
        · change h1 ∈ as.flatMap ReadyMatchReachability.sourceFieldHeaptypes
          exact List.mem_flatMap.mpr ⟨fieldA, hfieldA, hm1⟩

end properties.wasm_module_ok.MatchStructtypeLocal
