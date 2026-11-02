import properties.wasm_module_ok.MatchStorageConditional
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchFieldConditional

def fieldMatch (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool) :
    SpecTec.fieldtype → SpecTec.fieldtype → Bool
  | .FieldT .Cons a, .FieldT .Cons b =>
      MatchStorageConditional.storageMatch heapMatch a b
  | .FieldT .Var a, .FieldT .Var b =>
      MatchStorageConditional.storageMatch heapMatch a b &&
        MatchStorageConditional.storageMatch heapMatch b a
  | _, _ => false

theorem field_cons_forward_true
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.storagetype) (n : Nat)
    (hforward : MatchStorageConditional.storageMatch heapMatch a b = true) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts
        (.FieldT .Cons a) (.FieldT .Cons b)⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_fieldtype_clauses» dts
        (.FieldT .Cons a) (.FieldT .Cons b)))
    n (.success (.of true)) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$match_fieldtype:clause:0» dts
      (.FieldT .Cons a) (.FieldT .Cons b))
    n (.success (.of true)) n
  unfold SpecTec.«$match_fieldtype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · simpa [hforward] using
      (MatchStorageConditional.match_storage_total_of_heap
        dts heapMatch hheap a b n)
  · exact SpecTecExecution.Eval.bind_success
      (SpecTecExecution.Eval.guard_true (by simp [hforward]))
      (SpecTecExecution.Eval.pure true)

theorem field_cons_forward_false
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.storagetype) (n : Nat)
    (hforward : MatchStorageConditional.storageMatch heapMatch a b = false) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts
        (.FieldT .Cons a) (.FieldT .Cons b)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_fieldtype_clauses» dts
        (.FieldT .Cons a) (.FieldT .Cons b)))
    n (.success (.of false)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_fieldtype:clause:0» dts
        (.FieldT .Cons a) (.FieldT .Cons b)) n .unmatch n
    unfold SpecTec.«$match_fieldtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact MatchStorageConditional.match_storage_total_of_heap
        dts heapMatch hheap a b n
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp [hforward]))
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_fieldtype:clause:1» dts
          (.FieldT .Cons a) (.FieldT .Cons b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageConditional.match_storage_total_of_heap
          dts heapMatch hheap a b n
      · apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageConditional.match_storage_total_of_heap
            dts heapMatch hheap b a n
        · exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by simp [hforward]))
    · apply SpecTecExecution.tryClauses_cons_success
      exact SpecTecExecution.Eval.pure false

theorem field_var_var_total
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.storagetype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts
        (.FieldT .Var a) (.FieldT .Var b)⟩)
      n (.success (.of
        (fieldMatch heapMatch (.FieldT .Var a) (.FieldT .Var b)))) n := by
  by_cases hboth :
      MatchStorageConditional.storageMatch heapMatch a b = true ∧
      MatchStorageConditional.storageMatch heapMatch b a = true
  · have hresult : fieldMatch heapMatch (.FieldT .Var a) (.FieldT .Var b) = true := by
      simp [fieldMatch, hboth.1, hboth.2]
    rw [hresult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_fieldtype_clauses» dts
          (.FieldT .Var a) (.FieldT .Var b)))
      n (.success (.of true)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_fieldtype:clause:0» dts
          (.FieldT .Var a) (.FieldT .Var b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageConditional.match_storage_total_of_heap
          dts heapMatch hheap a b n
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp))
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_fieldtype:clause:1» dts
          (.FieldT .Var a) (.FieldT .Var b))
        n (.success (.of true)) n
      unfold SpecTec.«$match_fieldtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageConditional.match_storage_total_of_heap
          dts heapMatch hheap a b n
      · apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageConditional.match_storage_total_of_heap
            dts heapMatch hheap b a n
        · exact SpecTecExecution.Eval.bind_success
            (SpecTecExecution.Eval.guard_true (by simp [hboth.1, hboth.2]))
            (SpecTecExecution.Eval.pure true)
  · have hresult : fieldMatch heapMatch (.FieldT .Var a) (.FieldT .Var b) = false := by
      cases hf : MatchStorageConditional.storageMatch heapMatch a b <;>
        cases hr : MatchStorageConditional.storageMatch heapMatch b a <;>
        simp_all [fieldMatch]
    rw [hresult]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_fieldtype_clauses» dts
          (.FieldT .Var a) (.FieldT .Var b)))
      n (.success (.of false)) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_fieldtype:clause:0» dts
          (.FieldT .Var a) (.FieldT .Var b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageConditional.match_storage_total_of_heap
          dts heapMatch hheap a b n
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp))
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_fieldtype:clause:1» dts
            (.FieldT .Var a) (.FieldT .Var b)) n .unmatch n
        unfold SpecTec.«$match_fieldtype:clause:1»
        apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageConditional.match_storage_total_of_heap
            dts heapMatch hheap a b n
        · apply SpecTecExecution.Eval.bind_success
          · exact MatchStorageConditional.match_storage_total_of_heap
              dts heapMatch hheap b a n
          · exact SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false (by simpa using hboth))
      · apply SpecTecExecution.tryClauses_cons_success
        exact SpecTecExecution.Eval.pure false

theorem field_mixed_total
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (m₁ m₂ : SpecTec.«mut») (a b : SpecTec.storagetype) (n : Nat)
    (hmixed : m₁ ≠ m₂) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts
        (.FieldT m₁ a) (.FieldT m₂ b)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_fieldtype_clauses» dts
        (.FieldT m₁ a) (.FieldT m₂ b)))
    n (.success (.of false)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_fieldtype:clause:0» dts
        (.FieldT m₁ a) (.FieldT m₂ b)) n .unmatch n
    unfold SpecTec.«$match_fieldtype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact MatchStorageConditional.match_storage_total_of_heap
        dts heapMatch hheap a b n
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp [hmixed]))
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_fieldtype:clause:1» dts
          (.FieldT m₁ a) (.FieldT m₂ b)) n .unmatch n
      unfold SpecTec.«$match_fieldtype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchStorageConditional.match_storage_total_of_heap
          dts heapMatch hheap a b n
      · apply SpecTecExecution.Eval.bind_success
        · exact MatchStorageConditional.match_storage_total_of_heap
            dts heapMatch hheap b a n
        · exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by simp [hmixed]))
    · apply SpecTecExecution.tryClauses_cons_success
      exact SpecTecExecution.Eval.pure false

theorem match_field_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.fieldtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a b⟩)
      n (.success (.of (fieldMatch heapMatch a b))) n := by
  cases a with
  | FieldT m₁ a =>
    cases b with
    | FieldT m₂ b =>
      cases m₁ with
      | Cons =>
        cases m₂ with
        | Cons =>
          cases hf : MatchStorageConditional.storageMatch heapMatch a b with
          | true =>
            simpa [fieldMatch, hf] using
              (field_cons_forward_true dts heapMatch hheap a b n hf)
          | false =>
            simpa [fieldMatch, hf] using
              (field_cons_forward_false dts heapMatch hheap a b n hf)
        | Var =>
          simpa [fieldMatch] using
            (field_mixed_total dts heapMatch hheap .Cons .Var a b n (by decide))
      | Var =>
        cases m₂ with
        | Cons =>
          simpa [fieldMatch] using
            (field_mixed_total dts heapMatch hheap .Var .Cons a b n (by decide))
        | Var => exact field_var_var_total dts heapMatch hheap a b n

theorem match_field_success_iff_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.fieldtype) (result : Bool) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_fieldtype» dts a b⟩)
      n (.success (.of result)) finish ↔
    result = fieldMatch heapMatch a b ∧ finish = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (match_field_total_of_heap dts heapMatch hheap a b n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact match_field_total_of_heap dts heapMatch hheap a b finish

end properties.wasm_module_ok.MatchFieldConditional
