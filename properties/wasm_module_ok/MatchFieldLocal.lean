import properties.wasm_module_ok.MatchFieldConditional
import properties.wasm_module_ok.MatchStorageLocal

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchFieldLocal

theorem field_cons_forward_true_local
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.storagetype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply)
    (hforward : MatchStorageConditional.storageMatch heapMatch a b = true) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» dts
        (.FieldT .Cons a) (.FieldT .Cons b)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_fieldtype_clauses» dts
        (.FieldT .Cons a) (.FieldT .Cons b)) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_fieldtype:clause:0» dts
      (.FieldT .Cons a) (.FieldT .Cons b))
    n (.success (.of true)) n
  unfold SpecTec.«$match_fieldtype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · simpa [hforward] using
      (MatchStorageLocal.match_storage_total_of_local_heap
        dts heapMatch a b n hheap)
  · exact SpecTecExecution.Eval.bind_success
      (SpecTecExecution.Eval.guard_true (by simp))
      (SpecTecExecution.Eval.pure true)

theorem field_cons_forward_false_local
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.storagetype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        supply (.success (.of (heapMatch h2 h1))) supply)
    (hforward : MatchStorageConditional.storageMatch heapMatch a b = false) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» dts
        (.FieldT .Cons a) (.FieldT .Cons b)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_fieldtype_clauses» dts
        (.FieldT .Cons a) (.FieldT .Cons b)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_fieldtype:clause:0» dts
        (.FieldT .Cons a) (.FieldT .Cons b)) n .unmatch n
    unfold SpecTec.«$match_fieldtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact MatchStorageLocal.match_storage_total_of_local_heap
        dts heapMatch a b n hheap
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp [hforward]))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:1» dts
          (.FieldT .Cons a) (.FieldT .Cons b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageLocal.match_storage_total_of_local_heap
          dts heapMatch a b n hheap
      · apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageLocal.match_storage_total_of_local_heap
            dts heapMatch b a n hheapReverse
        · exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by simp [hforward]))
    · apply SpecTecExecution.firstSuccess_cons_success
      exact SpecTecExecution.Eval.pure false

theorem field_var_var_total_local
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.storagetype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        supply (.success (.of (heapMatch h2 h1))) supply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» dts
        (.FieldT .Var a) (.FieldT .Var b)⟩)
      n (.success (.of
        (MatchFieldConditional.fieldMatch heapMatch
          (.FieldT .Var a) (.FieldT .Var b)))) n := by
  by_cases hboth :
      MatchStorageConditional.storageMatch heapMatch a b = true ∧
      MatchStorageConditional.storageMatch heapMatch b a = true
  · have hresult : MatchFieldConditional.fieldMatch heapMatch
        (.FieldT .Var a) (.FieldT .Var b) = true := by
      simp [MatchFieldConditional.fieldMatch, hboth.1, hboth.2]
    rw [hresult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_fieldtype_clauses» dts
          (.FieldT .Var a) (.FieldT .Var b)) ())
      n (.success (.of true)) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:0» dts
          (.FieldT .Var a) (.FieldT .Var b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageLocal.match_storage_total_of_local_heap
          dts heapMatch a b n hheap
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp))
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:1» dts
          (.FieldT .Var a) (.FieldT .Var b))
        n (.success (.of true)) n
      unfold SpecTec.«$match_fieldtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageLocal.match_storage_total_of_local_heap
          dts heapMatch a b n hheap
      · apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageLocal.match_storage_total_of_local_heap
            dts heapMatch b a n hheapReverse
        · exact SpecTecExecution.Eval.bind_success
            (SpecTecExecution.Eval.guard_true (by simp [hboth.1, hboth.2]))
            (SpecTecExecution.Eval.pure true)
  · have hresult : MatchFieldConditional.fieldMatch heapMatch
        (.FieldT .Var a) (.FieldT .Var b) = false := by
      cases hf : MatchStorageConditional.storageMatch heapMatch a b <;>
        cases hr : MatchStorageConditional.storageMatch heapMatch b a <;>
        simp_all [MatchFieldConditional.fieldMatch]
    rw [hresult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_fieldtype_clauses» dts
          (.FieldT .Var a) (.FieldT .Var b)) ())
      n (.success (.of false)) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:0» dts
          (.FieldT .Var a) (.FieldT .Var b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageLocal.match_storage_total_of_local_heap
          dts heapMatch a b n hheap
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp))
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_fieldtype:clause:1» dts
            (.FieldT .Var a) (.FieldT .Var b)) n .unmatch n
        unfold SpecTec.«$match_fieldtype:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageLocal.match_storage_total_of_local_heap
            dts heapMatch a b n hheap
        · apply SpecTecExecution.Eval.bind_success
          · exact MatchStorageLocal.match_storage_total_of_local_heap
              dts heapMatch b a n hheapReverse
          · exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false (by simpa using hboth))
      · apply SpecTecExecution.firstSuccess_cons_success
        exact SpecTecExecution.Eval.pure false

theorem field_mixed_total_local
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (m₁ m₂ : SpecTec.«mut») (a b : SpecTec.storagetype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        supply (.success (.of (heapMatch h2 h1))) supply)
    (hmixed : m₁ ≠ m₂) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» dts
        (.FieldT m₁ a) (.FieldT m₂ b)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_fieldtype_clauses» dts
        (.FieldT m₁ a) (.FieldT m₂ b)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_fieldtype:clause:0» dts
        (.FieldT m₁ a) (.FieldT m₂ b)) n .unmatch n
    unfold SpecTec.«$match_fieldtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact MatchStorageLocal.match_storage_total_of_local_heap
        dts heapMatch a b n hheap
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp [hmixed]))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:1» dts
          (.FieldT m₁ a) (.FieldT m₂ b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageLocal.match_storage_total_of_local_heap
          dts heapMatch a b n hheap
      · apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageLocal.match_storage_total_of_local_heap
            dts heapMatch b a n hheapReverse
        · exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by simp [hmixed]))
    · apply SpecTecExecution.firstSuccess_cons_success
      exact SpecTecExecution.Eval.pure false

theorem match_field_total_of_local_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.fieldtype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceFieldHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceFieldHeaptypes b →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceFieldHeaptypes b →
      h1 ∈ ReadyMatchReachability.sourceFieldHeaptypes a →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        supply (.success (.of (heapMatch h2 h1))) supply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» dts a b⟩)
      n (.success (.of (MatchFieldConditional.fieldMatch heapMatch a b))) n := by
  cases a with
  | FieldT m₁ a =>
    cases b with
    | FieldT m₂ b =>
      have hAB : ∀ h1 h2,
          h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
          h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
          ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
            (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
            supply (.success (.of (heapMatch h1 h2))) supply := by
        intro h1 h2 hm1 hm2 supply
        exact hheap h1 h2 hm1 hm2 supply
      have hBA : ∀ h2 h1,
          h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
          h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
          ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
            (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
            supply (.success (.of (heapMatch h2 h1))) supply := by
        intro h2 h1 hm2 hm1 supply
        exact hheapReverse h2 h1 hm2 hm1 supply
      cases m₁ with
      | Cons =>
        cases m₂ with
        | Cons =>
          cases hf : MatchStorageConditional.storageMatch heapMatch a b with
          | true =>
            simpa [MatchFieldConditional.fieldMatch, hf] using
              (field_cons_forward_true_local dts heapMatch a b n hAB hf)
          | false =>
            simpa [MatchFieldConditional.fieldMatch, hf] using
              (field_cons_forward_false_local dts heapMatch a b n hAB hBA hf)
        | Var =>
          simpa [MatchFieldConditional.fieldMatch] using
            (field_mixed_total_local dts heapMatch .Cons .Var a b n
              hAB hBA (by decide))
      | Var =>
        cases m₂ with
        | Cons =>
          simpa [MatchFieldConditional.fieldMatch] using
            (field_mixed_total_local dts heapMatch .Var .Cons a b n
              hAB hBA (by decide))
        | Var =>
          exact field_var_var_total_local dts heapMatch a b n hAB hBA

theorem field_cons_forward_true_local_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.storagetype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (hforward : MatchStorageConditional.storageMatch heapMatch a b = true) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» dts
        (.FieldT .Cons a) (.FieldT .Cons b)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_fieldtype_clauses» dts
        (.FieldT .Cons a) (.FieldT .Cons b)) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_fieldtype:clause:0» dts
      (.FieldT .Cons a) (.FieldT .Cons b))
    n (.success (.of true)) n
  unfold SpecTec.«$match_fieldtype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · simpa [hforward] using
      (MatchStorageLocal.match_storage_total_of_local_heap_at
        dts heapMatch a b n hheap)
  · exact SpecTecExecution.Eval.bind_success
      (SpecTecExecution.Eval.guard_true (by simp))
      (SpecTecExecution.Eval.pure true)

theorem field_cons_forward_false_local_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.storagetype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        n (.success (.of (heapMatch h2 h1))) n)
    (hforward : MatchStorageConditional.storageMatch heapMatch a b = false) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» dts
        (.FieldT .Cons a) (.FieldT .Cons b)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_fieldtype_clauses» dts
        (.FieldT .Cons a) (.FieldT .Cons b)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_fieldtype:clause:0» dts
        (.FieldT .Cons a) (.FieldT .Cons b)) n .unmatch n
    unfold SpecTec.«$match_fieldtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact MatchStorageLocal.match_storage_total_of_local_heap_at
        dts heapMatch a b n hheap
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp [hforward]))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:1» dts
          (.FieldT .Cons a) (.FieldT .Cons b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageLocal.match_storage_total_of_local_heap_at
          dts heapMatch a b n hheap
      · apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageLocal.match_storage_total_of_local_heap_at
            dts heapMatch b a n hheapReverse
        · exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by simp [hforward]))
    · apply SpecTecExecution.firstSuccess_cons_success
      exact SpecTecExecution.Eval.pure false

theorem field_var_var_total_local_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.storagetype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        n (.success (.of (heapMatch h2 h1))) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» dts
        (.FieldT .Var a) (.FieldT .Var b)⟩)
      n (.success (.of
        (MatchFieldConditional.fieldMatch heapMatch
          (.FieldT .Var a) (.FieldT .Var b)))) n := by
  by_cases hboth :
      MatchStorageConditional.storageMatch heapMatch a b = true ∧
      MatchStorageConditional.storageMatch heapMatch b a = true
  · have hresult : MatchFieldConditional.fieldMatch heapMatch
        (.FieldT .Var a) (.FieldT .Var b) = true := by
      simp [MatchFieldConditional.fieldMatch, hboth.1, hboth.2]
    rw [hresult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_fieldtype_clauses» dts
          (.FieldT .Var a) (.FieldT .Var b)) ())
      n (.success (.of true)) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:0» dts
          (.FieldT .Var a) (.FieldT .Var b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageLocal.match_storage_total_of_local_heap_at
          dts heapMatch a b n hheap
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp))
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:1» dts
          (.FieldT .Var a) (.FieldT .Var b))
        n (.success (.of true)) n
      unfold SpecTec.«$match_fieldtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageLocal.match_storage_total_of_local_heap_at
          dts heapMatch a b n hheap
      · apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageLocal.match_storage_total_of_local_heap_at
            dts heapMatch b a n hheapReverse
        · exact SpecTecExecution.Eval.bind_success
            (SpecTecExecution.Eval.guard_true (by simp [hboth.1, hboth.2]))
            (SpecTecExecution.Eval.pure true)
  · have hresult : MatchFieldConditional.fieldMatch heapMatch
        (.FieldT .Var a) (.FieldT .Var b) = false := by
      cases hf : MatchStorageConditional.storageMatch heapMatch a b <;>
        cases hr : MatchStorageConditional.storageMatch heapMatch b a <;>
        simp_all [MatchFieldConditional.fieldMatch]
    rw [hresult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$match_fieldtype_clauses» dts
          (.FieldT .Var a) (.FieldT .Var b)) ())
      n (.success (.of false)) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:0» dts
          (.FieldT .Var a) (.FieldT .Var b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageLocal.match_storage_total_of_local_heap_at
          dts heapMatch a b n hheap
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp))
    · apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_fieldtype:clause:1» dts
            (.FieldT .Var a) (.FieldT .Var b)) n .unmatch n
        unfold SpecTec.«$match_fieldtype:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageLocal.match_storage_total_of_local_heap_at
            dts heapMatch a b n hheap
        · apply SpecTecExecution.Eval.bind_success
          · exact MatchStorageLocal.match_storage_total_of_local_heap_at
              dts heapMatch b a n hheapReverse
          · exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false (by simpa using hboth))
      · apply SpecTecExecution.firstSuccess_cons_success
        exact SpecTecExecution.Eval.pure false

theorem field_mixed_total_local_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (m₁ m₂ : SpecTec.«mut») (a b : SpecTec.storagetype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        n (.success (.of (heapMatch h2 h1))) n)
    (hmixed : m₁ ≠ m₂) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» dts
        (.FieldT m₁ a) (.FieldT m₂ b)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_fieldtype_clauses» dts
        (.FieldT m₁ a) (.FieldT m₂ b)) ())
    n (.success (.of false)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_fieldtype:clause:0» dts
        (.FieldT m₁ a) (.FieldT m₂ b)) n .unmatch n
    unfold SpecTec.«$match_fieldtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact MatchStorageLocal.match_storage_total_of_local_heap_at
        dts heapMatch a b n hheap
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp [hmixed]))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_fieldtype:clause:1» dts
          (.FieldT m₁ a) (.FieldT m₂ b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageLocal.match_storage_total_of_local_heap_at
          dts heapMatch a b n hheap
      · apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageLocal.match_storage_total_of_local_heap_at
            dts heapMatch b a n hheapReverse
        · exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by simp [hmixed]))
    · apply SpecTecExecution.firstSuccess_cons_success
      exact SpecTecExecution.Eval.pure false

theorem match_field_total_of_local_heap_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.fieldtype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceFieldHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceFieldHeaptypes b →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceFieldHeaptypes b →
      h1 ∈ ReadyMatchReachability.sourceFieldHeaptypes a →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        n (.success (.of (heapMatch h2 h1))) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_fieldtype» dts a b⟩)
      n (.success (.of (MatchFieldConditional.fieldMatch heapMatch a b))) n := by
  cases a with
  | FieldT m₁ a =>
    cases b with
    | FieldT m₂ b =>
      have hAB : ∀ h1 h2,
          h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
          h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
          SpecTecExecution.Eval SpecTec.specTecProgram
            (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
            n (.success (.of (heapMatch h1 h2))) n := by
        intro h1 h2 hm1 hm2
        exact hheap h1 h2 hm1 hm2
      have hBA : ∀ h2 h1,
          h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
          h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
          SpecTecExecution.Eval SpecTec.specTecProgram
            (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
            n (.success (.of (heapMatch h2 h1))) n := by
        intro h2 h1 hm2 hm1
        exact hheapReverse h2 h1 hm2 hm1
      cases m₁ with
      | Cons =>
        cases m₂ with
        | Cons =>
          cases hf : MatchStorageConditional.storageMatch heapMatch a b with
          | true =>
            simpa [MatchFieldConditional.fieldMatch, hf] using
              (field_cons_forward_true_local_at dts heapMatch a b n hAB hf)
          | false =>
            simpa [MatchFieldConditional.fieldMatch, hf] using
              (field_cons_forward_false_local_at dts heapMatch a b n hAB hBA hf)
        | Var =>
          simpa [MatchFieldConditional.fieldMatch] using
            (field_mixed_total_local_at dts heapMatch .Cons .Var a b n
              hAB hBA (by decide))
      | Var =>
        cases m₂ with
        | Cons =>
          simpa [MatchFieldConditional.fieldMatch] using
            (field_mixed_total_local_at dts heapMatch .Var .Cons a b n
              hAB hBA (by decide))
        | Var =>
          exact field_var_var_total_local_at dts heapMatch a b n hAB hBA

end properties.wasm_module_ok.MatchFieldLocal
