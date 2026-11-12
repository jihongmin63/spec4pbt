import properties.wasm_module_ok.MatchFunctionConditional
import properties.wasm_module_ok.MatchResulttypeLocal

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchFunctionLocal

theorem match_functype_total_of_local_heap_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (ft₁ ft₂ : SpecTec.functype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT ft₁) →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT ft₂) →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT ft₂) →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT ft₁) →
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h2 h1⟩)
        n (.success (.of (heapMatch h2 h1))) n) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_functype» dts ft₁ ft₂⟩)
      n (.success (.of
        (MatchFunctionConditional.functionMatch heapMatch ft₁ ft₂))) n := by
  cases ft₁ with
  | FuncT inputs outputs =>
    cases ft₂ with
    | FuncT inputs' outputs' =>
      apply (MatchFunctypeCalls.match_functype_success_iff_calls
        dts inputs outputs inputs' outputs' n n
          (MatchFunctionConditional.functionMatch heapMatch
            (.FuncT inputs outputs) (.FuncT inputs' outputs'))).2
      refine ⟨n,
        MatchFunctionConditional.resultMatch heapMatch inputs' inputs,
        MatchFunctionConditional.resultMatch heapMatch outputs outputs',
        ?_, ?_, rfl⟩
      · apply MatchResulttypeLocal.match_resulttype_total_of_local_heap_at
        intro h2 h1 hm2 hm1
        apply hheapReverse h2 h1
        · change h2 ∈ (inputs' ++ outputs').flatMap
            ReadyMatchReachability.sourceValHeaptypes
          simp only [List.flatMap_append, List.mem_append]
          exact Or.inl hm2
        · change h1 ∈ (inputs ++ outputs).flatMap
            ReadyMatchReachability.sourceValHeaptypes
          simp only [List.flatMap_append, List.mem_append]
          exact Or.inl hm1
      · apply MatchResulttypeLocal.match_resulttype_total_of_local_heap_at
        intro h1 h2 hm1 hm2
        apply hheap h1 h2
        · change h1 ∈ (inputs ++ outputs).flatMap
            ReadyMatchReachability.sourceValHeaptypes
          simp only [List.flatMap_append, List.mem_append]
          exact Or.inr hm1
        · change h2 ∈ (inputs' ++ outputs').flatMap
            ReadyMatchReachability.sourceValHeaptypes
          simp only [List.flatMap_append, List.mem_append]
          exact Or.inr hm2

theorem match_functype_total_of_local_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (ft₁ ft₂ : SpecTec.functype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT ft₁) →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT ft₂) →
      ∀ supply, SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT ft₂) →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT ft₁) →
      ∀ supply, SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h2 h1⟩)
        supply (.success (.of (heapMatch h2 h1))) supply) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_functype» dts ft₁ ft₂⟩)
      n (.success (.of
        (MatchFunctionConditional.functionMatch heapMatch ft₁ ft₂))) n := by
  cases ft₁ with
  | FuncT inputs outputs =>
    cases ft₂ with
    | FuncT inputs' outputs' =>
      apply (MatchFunctypeCalls.match_functype_success_iff_calls
        dts inputs outputs inputs' outputs' n n
          (MatchFunctionConditional.functionMatch heapMatch
            (.FuncT inputs outputs) (.FuncT inputs' outputs'))).2
      refine ⟨n,
        MatchFunctionConditional.resultMatch heapMatch inputs' inputs,
        MatchFunctionConditional.resultMatch heapMatch outputs outputs',
        ?_, ?_, rfl⟩
      · apply MatchResulttypeLocal.match_resulttype_total_of_local_heap
        intro h2 h1 hm2 hm1 supply
        apply hheapReverse h2 h1
        · change h2 ∈ (inputs' ++ outputs').flatMap
            ReadyMatchReachability.sourceValHeaptypes
          simp only [List.flatMap_append, List.mem_append]
          exact Or.inl hm2
        · change h1 ∈ (inputs ++ outputs).flatMap
            ReadyMatchReachability.sourceValHeaptypes
          simp only [List.flatMap_append, List.mem_append]
          exact Or.inl hm1
      · apply MatchResulttypeLocal.match_resulttype_total_of_local_heap
        intro h1 h2 hm1 hm2 supply
        apply hheap h1 h2
        · change h1 ∈ (inputs ++ outputs).flatMap
            ReadyMatchReachability.sourceValHeaptypes
          simp only [List.flatMap_append, List.mem_append]
          exact Or.inr hm1
        · change h2 ∈ (inputs' ++ outputs').flatMap
            ReadyMatchReachability.sourceValHeaptypes
          simp only [List.flatMap_append, List.mem_append]
          exact Or.inr hm2

end properties.wasm_module_ok.MatchFunctionLocal
