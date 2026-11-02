import properties.wasm_module_ok.MatchStorageConditional
import properties.wasm_module_ok.MatchValtypeLocal

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchStorageLocal

theorem match_storage_total_of_local_heap_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.storagetype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_storagetype» dts a b⟩)
      n (.success (.of
        (MatchStorageConditional.storageMatch heapMatch a b))) n := by
  cases a with
  | ValStorageT a =>
    cases b with
    | ValStorageT b =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$match_storagetype_clauses» dts
            (.ValStorageT a) (.ValStorageT b)))
        n (.success (.of
          (MatchStorageConditional.storageMatch heapMatch
            (.ValStorageT a) (.ValStorageT b)))) n
      apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_storagetype:clause:0» dts
          (.ValStorageT a) (.ValStorageT b))
        n (.success (.of
          (MatchStorageConditional.storageMatch heapMatch
            (.ValStorageT a) (.ValStorageT b)))) n
      unfold SpecTec.«$match_storagetype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success
          · apply MatchValtypeLocal.match_valtype_total_of_local_heap_at
            intro h1 h2 hm1 hm2
            exact hheap h1 h2 hm1 hm2
          · exact SpecTecExecution.Eval.pure
              (MatchStorageConditional.storageMatch heapMatch
                (.ValStorageT a) (.ValStorageT b))
    | PackStorageT b =>
      exact MatchStorageConditional.match_storage_val_pack_total
        dts heapMatch a b n
  | PackStorageT a =>
    cases b with
    | ValStorageT b =>
      exact MatchStorageConditional.match_storage_pack_val_total
        dts heapMatch a b n
    | PackStorageT b =>
      exact MatchStorageConditional.match_storage_pack_pair_total
        dts heapMatch a b n

theorem match_storage_total_of_local_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.storagetype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceStorageHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceStorageHeaptypes b →
      ∀ supply, SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_storagetype» dts a b⟩)
      n (.success (.of
        (MatchStorageConditional.storageMatch heapMatch a b))) n := by
  apply match_storage_total_of_local_heap_at
  intro h1 h2 hm1 hm2
  exact hheap h1 h2 hm1 hm2 n

end properties.wasm_module_ok.MatchStorageLocal
