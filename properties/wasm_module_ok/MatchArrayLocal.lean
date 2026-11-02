import properties.wasm_module_ok.MatchArrayConditional
import properties.wasm_module_ok.MatchFieldLocal

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchArrayLocal

theorem match_array_total_of_local_heap_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.arraytype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefArrayT a) →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefArrayT b) →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefArrayT b) →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefArrayT a) →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        n (.success (.of (heapMatch h2 h1))) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_arraytype» dts a b⟩)
      n (.success (.of (MatchArrayConditional.arrayMatch heapMatch a b))) n := by
  cases a with
  | ArrayT a =>
    cases b with
    | ArrayT b =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$match_arraytype_clauses» dts
            (.ArrayT a) (.ArrayT b)) ())
        n (.success (.of
          (MatchArrayConditional.arrayMatch heapMatch (.ArrayT a) (.ArrayT b)))) n
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_arraytype:clause:0» dts
          (.ArrayT a) (.ArrayT b))
        n (.success (.of
          (MatchArrayConditional.arrayMatch heapMatch (.ArrayT a) (.ArrayT b)))) n
      unfold SpecTec.«$match_arraytype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · apply MatchFieldLocal.match_field_total_of_local_heap_at
        · intro h1 h2 hm1 hm2
          exact hheap h1 h2 hm1 hm2
        · intro h2 h1 hm2 hm1
          exact hheapReverse h2 h1 hm2 hm1
      · exact SpecTecExecution.Eval.pure
          (MatchArrayConditional.arrayMatch heapMatch (.ArrayT a) (.ArrayT b))

theorem match_array_total_of_local_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.arraytype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefArrayT a) →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefArrayT b) →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefArrayT b) →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefArrayT a) →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        supply (.success (.of (heapMatch h2 h1))) supply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_arraytype» dts a b⟩)
      n (.success (.of (MatchArrayConditional.arrayMatch heapMatch a b))) n := by
  cases a with
  | ArrayT a =>
    cases b with
    | ArrayT b =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$match_arraytype_clauses» dts
            (.ArrayT a) (.ArrayT b)) ())
        n (.success (.of
          (MatchArrayConditional.arrayMatch heapMatch (.ArrayT a) (.ArrayT b)))) n
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_arraytype:clause:0» dts
          (.ArrayT a) (.ArrayT b))
        n (.success (.of
          (MatchArrayConditional.arrayMatch heapMatch (.ArrayT a) (.ArrayT b)))) n
      unfold SpecTec.«$match_arraytype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · apply MatchFieldLocal.match_field_total_of_local_heap
        · intro h1 h2 hm1 hm2 supply
          exact hheap h1 h2 hm1 hm2 supply
        · intro h2 h1 hm2 hm1 supply
          exact hheapReverse h2 h1 hm2 hm1 supply
      · exact SpecTecExecution.Eval.pure
          (MatchArrayConditional.arrayMatch heapMatch (.ArrayT a) (.ArrayT b))

end properties.wasm_module_ok.MatchArrayLocal
