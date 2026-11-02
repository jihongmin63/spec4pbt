import properties.wasm_module_ok.MatchValtypeConditional
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchStorageConditional

def storageMatch (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool) :
    SpecTec.storagetype → SpecTec.storagetype → Bool
  | .ValStorageT a, .ValStorageT b =>
      MatchValtypeConditional.matchValtypeResult heapMatch a b
  | .PackStorageT a, .PackStorageT b => decide (a = b)
  | _, _ => false

theorem match_packtype_total (dts : List SpecTec.deftype)
    (a b : SpecTec.packtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_packtype» dts a b⟩)
      n (.success (.of (decide (a = b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_packtype_clauses» dts a b))
    n (.success (.of (decide (a = b)))) n
  apply SpecTecExecution.tryClauses_cons_success
  exact SpecTecExecution.Eval.pure (decide (a = b))

theorem match_storage_val_pair_total
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_storagetype» dts
        (.ValStorageT a) (.ValStorageT b)⟩)
      n (.success (.of
        (storageMatch heapMatch (.ValStorageT a) (.ValStorageT b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_storagetype_clauses» dts
        (.ValStorageT a) (.ValStorageT b)))
    n (.success (.of
      (storageMatch heapMatch (.ValStorageT a) (.ValStorageT b)))) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$match_storagetype:clause:0» dts
      (.ValStorageT a) (.ValStorageT b))
    n (.success (.of
      (storageMatch heapMatch (.ValStorageT a) (.ValStorageT b)))) n
  unfold SpecTec.«$match_storagetype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
      · exact MatchValtypeConditional.match_valtype_total_of_heap
          dts heapMatch hheap a b n
      · exact SpecTecExecution.Eval.pure
          (storageMatch heapMatch (.ValStorageT a) (.ValStorageT b))

theorem match_storage_pack_pair_total
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.packtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_storagetype» dts
        (.PackStorageT a) (.PackStorageT b)⟩)
      n (.success (.of
        (storageMatch heapMatch (.PackStorageT a) (.PackStorageT b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_storagetype_clauses» dts
        (.PackStorageT a) (.PackStorageT b)))
    n (.success (.of
      (storageMatch heapMatch (.PackStorageT a) (.PackStorageT b)))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_storagetype:clause:0» dts
        (.PackStorageT a) (.PackStorageT b)) n .unmatch n
    unfold SpecTec.«$match_storagetype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:storagetype:ValStorageT»]))
  · apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_storagetype:clause:1» dts
        (.PackStorageT a) (.PackStorageT b))
      n (.success (.of
        (storageMatch heapMatch (.PackStorageT a) (.PackStorageT b)))) n
    unfold SpecTec.«$match_storagetype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact match_packtype_total dts a b n
        · exact SpecTecExecution.Eval.pure
            (storageMatch heapMatch (.PackStorageT a) (.PackStorageT b))

theorem match_storage_val_pack_total
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a : SpecTec.valtype) (b : SpecTec.packtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_storagetype» dts
        (.ValStorageT a) (.PackStorageT b)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_storagetype_clauses» dts
        (.ValStorageT a) (.PackStorageT b)))
    n (.success (.of false)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_storagetype:clause:0» dts
        (.ValStorageT a) (.PackStorageT b)) n .unmatch n
    unfold SpecTec.«$match_storagetype:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:storagetype:ValStorageT»]))
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_storagetype:clause:1» dts
          (.ValStorageT a) (.PackStorageT b)) n .unmatch n
      unfold SpecTec.«$match_storagetype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:storagetype:PackStorageT»]))
    · apply SpecTecExecution.tryClauses_cons_success
      exact SpecTecExecution.Eval.pure false

theorem match_storage_pack_val_total
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a : SpecTec.packtype) (b : SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_storagetype» dts
        (.PackStorageT a) (.ValStorageT b)⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_storagetype_clauses» dts
        (.PackStorageT a) (.ValStorageT b)))
    n (.success (.of false)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_storagetype:clause:0» dts
        (.PackStorageT a) (.ValStorageT b)) n .unmatch n
    unfold SpecTec.«$match_storagetype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:storagetype:ValStorageT»]))
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_storagetype:clause:1» dts
          (.PackStorageT a) (.ValStorageT b)) n .unmatch n
      unfold SpecTec.«$match_storagetype:clause:1»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:storagetype:PackStorageT»]))
    · apply SpecTecExecution.tryClauses_cons_success
      exact SpecTecExecution.Eval.pure false

theorem match_storage_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.storagetype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_storagetype» dts a b⟩)
      n (.success (.of (storageMatch heapMatch a b))) n := by
  cases a with
  | ValStorageT a =>
    cases b with
    | ValStorageT b => exact match_storage_val_pair_total dts heapMatch hheap a b n
    | PackStorageT b => exact match_storage_val_pack_total dts heapMatch a b n
  | PackStorageT a =>
    cases b with
    | ValStorageT b => exact match_storage_pack_val_total dts heapMatch a b n
    | PackStorageT b => exact match_storage_pack_pair_total dts heapMatch a b n

theorem match_storage_success_iff_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.storagetype) (result : Bool) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_storagetype» dts a b⟩)
      n (.success (.of result)) finish ↔
    result = storageMatch heapMatch a b ∧ finish = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (match_storage_total_of_heap dts heapMatch hheap a b n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact match_storage_total_of_heap dts heapMatch hheap a b finish

end properties.wasm_module_ok.MatchStorageConditional
