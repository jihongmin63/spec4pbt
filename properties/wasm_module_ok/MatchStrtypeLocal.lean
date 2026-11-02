import properties.wasm_module_ok.MatchStrtypeConditional
import properties.wasm_module_ok.MatchStructtypeLocal
import properties.wasm_module_ok.MatchArrayLocal
import properties.wasm_module_ok.MatchFunctionLocal

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchStrtypeLocal

theorem struct_pair_total_of_local_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.structtype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT a) →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT b) →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT b) →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT a) →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        supply (.success (.of (heapMatch h2 h1))) supply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_strtype»
          dts (.DefStructT a) (.DefStructT b)⟩)
      n (.success (.of
        (MatchStrtypeConditional.strMatch heapMatch
          (.DefStructT a) (.DefStructT b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses»
        dts (.DefStructT a) (.DefStructT b)) ())
    n (.success (.of
      (MatchStrtypeConditional.strMatch heapMatch
        (.DefStructT a) (.DefStructT b)))) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_strtype:clause:0»
      dts (.DefStructT a) (.DefStructT b))
    n (.success (.of
      (MatchStrtypeConditional.strMatch heapMatch
        (.DefStructT a) (.DefStructT b)))) n
  unfold SpecTec.«$match_strtype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
        (MatchStructtypeLocal.match_structtype_total_of_local_heap
          dts heapMatch a b n hheap hheapReverse)
      exact SpecTecExecution.Eval.pure _

theorem array_pair_total_of_local_heap
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
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_strtype»
          dts (.DefArrayT a) (.DefArrayT b)⟩)
      n (.success (.of
        (MatchStrtypeConditional.strMatch heapMatch
          (.DefArrayT a) (.DefArrayT b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses»
        dts (.DefArrayT a) (.DefArrayT b)) ())
    n (.success (.of
      (MatchStrtypeConditional.strMatch heapMatch
        (.DefArrayT a) (.DefArrayT b)))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:0»
        dts (.DefArrayT a) (.DefArrayT b)) n .unmatch n
    unfold SpecTec.«$match_strtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:strtype:DefStructT»]))
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:1»
        dts (.DefArrayT a) (.DefArrayT b))
      n (.success (.of
        (MatchStrtypeConditional.strMatch heapMatch
          (.DefArrayT a) (.DefArrayT b)))) n
    unfold SpecTec.«$match_strtype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
          (MatchArrayLocal.match_array_total_of_local_heap
            dts heapMatch a b n hheap hheapReverse)
        exact SpecTecExecution.Eval.pure _

theorem func_pair_total_of_local_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.functype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT a) →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT b) →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT b) →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT a) →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        supply (.success (.of (heapMatch h2 h1))) supply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_strtype»
          dts (.DefFuncT a) (.DefFuncT b)⟩)
      n (.success (.of
        (MatchStrtypeConditional.strMatch heapMatch
          (.DefFuncT a) (.DefFuncT b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses»
        dts (.DefFuncT a) (.DefFuncT b)) ())
    n (.success (.of
      (MatchStrtypeConditional.strMatch heapMatch
        (.DefFuncT a) (.DefFuncT b)))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:0»
        dts (.DefFuncT a) (.DefFuncT b)) n .unmatch n
    unfold SpecTec.«$match_strtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:strtype:DefStructT»]))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:1»
          dts (.DefFuncT a) (.DefFuncT b)) n .unmatch n
      unfold SpecTec.«$match_strtype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:strtype:DefArrayT»]))
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:2»
          dts (.DefFuncT a) (.DefFuncT b))
        n (.success (.of
          (MatchStrtypeConditional.strMatch heapMatch
            (.DefFuncT a) (.DefFuncT b)))) n
      unfold SpecTec.«$match_strtype:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success
            (MatchFunctionLocal.match_functype_total_of_local_heap
              dts heapMatch a b n hheap hheapReverse)
          exact SpecTecExecution.Eval.pure _

theorem match_strtype_total_of_local_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.strtype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes b →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes b →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes a →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        supply (.success (.of (heapMatch h2 h1))) supply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» dts a b⟩)
      n (.success (.of (MatchStrtypeConditional.strMatch heapMatch a b))) n := by
  cases a with
  | DefStructT a =>
    cases b with
    | DefStructT b =>
      exact struct_pair_total_of_local_heap dts heapMatch a b n hheap hheapReverse
    | DefArrayT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefStructT a) (.DefArrayT b) n (by simp [MatchStrtypeConditional.strTag])
    | DefFuncT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefStructT a) (.DefFuncT b) n (by simp [MatchStrtypeConditional.strTag])
  | DefArrayT a =>
    cases b with
    | DefStructT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefArrayT a) (.DefStructT b) n (by simp [MatchStrtypeConditional.strTag])
    | DefArrayT b =>
      exact array_pair_total_of_local_heap dts heapMatch a b n hheap hheapReverse
    | DefFuncT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefArrayT a) (.DefFuncT b) n (by simp [MatchStrtypeConditional.strTag])
  | DefFuncT a =>
    cases b with
    | DefStructT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefFuncT a) (.DefStructT b) n (by simp [MatchStrtypeConditional.strTag])
    | DefArrayT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefFuncT a) (.DefArrayT b) n (by simp [MatchStrtypeConditional.strTag])
    | DefFuncT b =>
      exact func_pair_total_of_local_heap dts heapMatch a b n hheap hheapReverse

theorem struct_pair_total_of_local_heap_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.structtype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT a) →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT b) →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT b) →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefStructT a) →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        n (.success (.of (heapMatch h2 h1))) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_strtype»
          dts (.DefStructT a) (.DefStructT b)⟩)
      n (.success (.of
        (MatchStrtypeConditional.strMatch heapMatch
          (.DefStructT a) (.DefStructT b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses»
        dts (.DefStructT a) (.DefStructT b)) ())
    n (.success (.of
      (MatchStrtypeConditional.strMatch heapMatch
        (.DefStructT a) (.DefStructT b)))) n
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_strtype:clause:0»
      dts (.DefStructT a) (.DefStructT b))
    n (.success (.of
      (MatchStrtypeConditional.strMatch heapMatch
        (.DefStructT a) (.DefStructT b)))) n
  unfold SpecTec.«$match_strtype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
        (MatchStructtypeLocal.match_structtype_total_of_local_heap_at
          dts heapMatch a b n hheap hheapReverse)
      exact SpecTecExecution.Eval.pure _

theorem array_pair_total_of_local_heap_at
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
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_strtype»
          dts (.DefArrayT a) (.DefArrayT b)⟩)
      n (.success (.of
        (MatchStrtypeConditional.strMatch heapMatch
          (.DefArrayT a) (.DefArrayT b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses»
        dts (.DefArrayT a) (.DefArrayT b)) ())
    n (.success (.of
      (MatchStrtypeConditional.strMatch heapMatch
        (.DefArrayT a) (.DefArrayT b)))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:0»
        dts (.DefArrayT a) (.DefArrayT b)) n .unmatch n
    unfold SpecTec.«$match_strtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:strtype:DefStructT»]))
  · apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:1»
        dts (.DefArrayT a) (.DefArrayT b))
      n (.success (.of
        (MatchStrtypeConditional.strMatch heapMatch
          (.DefArrayT a) (.DefArrayT b)))) n
    unfold SpecTec.«$match_strtype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
          (MatchArrayLocal.match_array_total_of_local_heap_at
            dts heapMatch a b n hheap hheapReverse)
        exact SpecTecExecution.Eval.pure _

theorem func_pair_total_of_local_heap_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.functype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT a) →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT b) →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT b) →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes (.DefFuncT a) →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        n (.success (.of (heapMatch h2 h1))) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,
        SpecTec.SpecTecCall.«$match_strtype»
          dts (.DefFuncT a) (.DefFuncT b)⟩)
      n (.success (.of
        (MatchStrtypeConditional.strMatch heapMatch
          (.DefFuncT a) (.DefFuncT b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_strtype_clauses»
        dts (.DefFuncT a) (.DefFuncT b)) ())
    n (.success (.of
      (MatchStrtypeConditional.strMatch heapMatch
        (.DefFuncT a) (.DefFuncT b)))) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_strtype:clause:0»
        dts (.DefFuncT a) (.DefFuncT b)) n .unmatch n
    unfold SpecTec.«$match_strtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:strtype:DefStructT»]))
  · apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:1»
          dts (.DefFuncT a) (.DefFuncT b)) n .unmatch n
      unfold SpecTec.«$match_strtype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:strtype:DefArrayT»]))
    · apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_strtype:clause:2»
          dts (.DefFuncT a) (.DefFuncT b))
        n (.success (.of
          (MatchStrtypeConditional.strMatch heapMatch
            (.DefFuncT a) (.DefFuncT b)))) n
      unfold SpecTec.«$match_strtype:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success
            (MatchFunctionLocal.match_functype_total_of_local_heap_at
              dts heapMatch a b n hheap hheapReverse)
          exact SpecTecExecution.Eval.pure _

theorem match_strtype_total_of_local_heap_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.strtype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceHeaptypes a →
      h2 ∈ ReadyMatchReachability.sourceHeaptypes b →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (hheapReverse : ∀ h2 h1,
      h2 ∈ ReadyMatchReachability.sourceHeaptypes b →
      h1 ∈ ReadyMatchReachability.sourceHeaptypes a →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h2 h1⟩)
        n (.success (.of (heapMatch h2 h1))) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_strtype» dts a b⟩)
      n (.success (.of (MatchStrtypeConditional.strMatch heapMatch a b))) n := by
  cases a with
  | DefStructT a =>
    cases b with
    | DefStructT b =>
      exact struct_pair_total_of_local_heap_at dts heapMatch a b n hheap hheapReverse
    | DefArrayT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefStructT a) (.DefArrayT b) n (by simp [MatchStrtypeConditional.strTag])
    | DefFuncT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefStructT a) (.DefFuncT b) n (by simp [MatchStrtypeConditional.strTag])
  | DefArrayT a =>
    cases b with
    | DefStructT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefArrayT a) (.DefStructT b) n (by simp [MatchStrtypeConditional.strTag])
    | DefArrayT b =>
      exact array_pair_total_of_local_heap_at dts heapMatch a b n hheap hheapReverse
    | DefFuncT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefArrayT a) (.DefFuncT b) n (by simp [MatchStrtypeConditional.strTag])
  | DefFuncT a =>
    cases b with
    | DefStructT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefFuncT a) (.DefStructT b) n (by simp [MatchStrtypeConditional.strTag])
    | DefArrayT b =>
      exact MatchStrtypeConditional.mixed_pair_false
        dts (.DefFuncT a) (.DefArrayT b) n (by simp [MatchStrtypeConditional.strTag])
    | DefFuncT b =>
      exact func_pair_total_of_local_heap_at dts heapMatch a b n hheap hheapReverse

end properties.wasm_module_ok.MatchStrtypeLocal
