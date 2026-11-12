import properties.wasm_module_ok.MatchFunctionConditional
import properties.wasm_module_ok.MatchStructtypeConditional
import properties.wasm_module_ok.MatchArrayConditional
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchStrtypeConditional

def strMatch
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool) :
    SpecTec.strtype → SpecTec.strtype → Bool
  | .DefStructT a, .DefStructT b =>
      MatchStructtypeConditional.structMatch
        (MatchFieldConditional.fieldMatch heapMatch) a b
  | .DefArrayT a, .DefArrayT b =>
      MatchArrayConditional.arrayMatch heapMatch a b
  | .DefFuncT a, .DefFuncT b =>
      MatchFunctionConditional.functionMatch heapMatch a b
  | _, _ => false

def strTag : SpecTec.strtype → Nat
  | .DefStructT _ => 0
  | .DefArrayT _ => 1
  | .DefFuncT _ => 2

theorem struct_pair_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.structtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_strtype»
          dts (.DefStructT a) (.DefStructT b)⟩)
      n (.success (.of
        (strMatch heapMatch (.DefStructT a) (.DefStructT b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_strtype_clauses»
        dts (.DefStructT a) (.DefStructT b)))
    n (.success (.of
      (strMatch heapMatch (.DefStructT a) (.DefStructT b)))) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«$match_strtype:clause:0»
      dts (.DefStructT a) (.DefStructT b))
    n (.success (.of
      (strMatch heapMatch (.DefStructT a) (.DefStructT b)))) n
  unfold SpecTec.«$match_strtype:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
        (MatchStructtypeConditional.match_structtype_total_of_heap
          dts heapMatch hheap a b n)
      exact SpecTecExecution.Eval.pure _

theorem array_pair_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.arraytype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_strtype»
          dts (.DefArrayT a) (.DefArrayT b)⟩)
      n (.success (.of
        (strMatch heapMatch (.DefArrayT a) (.DefArrayT b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_strtype_clauses»
        dts (.DefArrayT a) (.DefArrayT b)))
    n (.success (.of
      (strMatch heapMatch (.DefArrayT a) (.DefArrayT b)))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_strtype:clause:0»
        dts (.DefArrayT a) (.DefArrayT b)) n .unmatch n
    unfold SpecTec.«$match_strtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:strtype:DefStructT»]))
  · apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_strtype:clause:1»
        dts (.DefArrayT a) (.DefArrayT b))
      n (.success (.of
        (strMatch heapMatch (.DefArrayT a) (.DefArrayT b)))) n
    unfold SpecTec.«$match_strtype:clause:1»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
          (MatchArrayConditional.match_array_total_of_heap
            dts heapMatch hheap a b n)
        exact SpecTecExecution.Eval.pure _

theorem func_pair_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.functype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_strtype»
          dts (.DefFuncT a) (.DefFuncT b)⟩)
      n (.success (.of
        (strMatch heapMatch (.DefFuncT a) (.DefFuncT b)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_strtype_clauses»
        dts (.DefFuncT a) (.DefFuncT b)))
    n (.success (.of
      (strMatch heapMatch (.DefFuncT a) (.DefFuncT b)))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_strtype:clause:0»
        dts (.DefFuncT a) (.DefFuncT b)) n .unmatch n
    unfold SpecTec.«$match_strtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false (by
        simp [SpecTec.«exec:match:strtype:DefStructT»]))
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_strtype:clause:1»
          dts (.DefFuncT a) (.DefFuncT b)) n .unmatch n
      unfold SpecTec.«$match_strtype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by
          simp [SpecTec.«exec:match:strtype:DefArrayT»]))
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_strtype:clause:2»
          dts (.DefFuncT a) (.DefFuncT b))
        n (.success (.of
          (strMatch heapMatch (.DefFuncT a) (.DefFuncT b)))) n
      unfold SpecTec.«$match_strtype:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success
            (MatchFunctionConditional.functype_total_of_heap
              dts heapMatch hheap a b n)
          exact SpecTecExecution.Eval.pure _

theorem mixed_pair_false
    (dts : List SpecTec.deftype)
    (a b : SpecTec.strtype) (n : Nat)
    (hmixed : strTag a ≠ strTag b) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_strtype» dts a b⟩)
      n (.success (.of false)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_strtype_clauses» dts a b))
    n (.success (.of false)) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_strtype:clause:0» dts a b) n .unmatch n
    unfold SpecTec.«$match_strtype:clause:0»
    cases ha : SpecTec.«exec:match:strtype:DefStructT» a with
    | false =>
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp [ha]))
    | true =>
      cases a <;> cases b <;>
        simp [strTag, SpecTec.«exec:match:strtype:DefStructT»] at hmixed ha
      all_goals exact (SpecTecExecution.Eval.bind_success
        (SpecTecExecution.Eval.guard_true rfl)
        (SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:strtype:DefStructT»]))))
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_strtype:clause:1» dts a b) n .unmatch n
      unfold SpecTec.«$match_strtype:clause:1»
      cases ha : SpecTec.«exec:match:strtype:DefArrayT» a with
      | false =>
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false (by simp [ha]))
      | true =>
        cases a <;> cases b <;>
          simp [strTag, SpecTec.«exec:match:strtype:DefArrayT»] at hmixed ha
        all_goals exact (SpecTecExecution.Eval.bind_success
          (SpecTecExecution.Eval.guard_true rfl)
          (SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by
              simp [SpecTec.«exec:match:strtype:DefArrayT»]))))
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«$match_strtype:clause:2» dts a b) n .unmatch n
        unfold SpecTec.«$match_strtype:clause:2»
        cases ha : SpecTec.«exec:match:strtype:DefFuncT» a with
        | false =>
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false (by simp [ha]))
        | true =>
          cases a <;> cases b <;>
            simp [strTag, SpecTec.«exec:match:strtype:DefFuncT»] at hmixed ha
          all_goals exact (SpecTecExecution.Eval.bind_success
            (SpecTecExecution.Eval.guard_true rfl)
            (SpecTecExecution.Eval.bind_unmatch
              (SpecTecExecution.Eval.guard_false (by
                simp [SpecTec.«exec:match:strtype:DefFuncT»]))))
      · apply SpecTecExecution.tryClauses_cons_success
        exact SpecTecExecution.Eval.pure false

theorem match_strtype_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.strtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_strtype» dts a b⟩)
      n (.success (.of (strMatch heapMatch a b))) n := by
  cases a with
  | DefStructT a =>
    cases b with
    | DefStructT b => exact struct_pair_total_of_heap dts heapMatch hheap a b n
    | DefArrayT b => exact mixed_pair_false dts (.DefStructT a) (.DefArrayT b) n (by simp [strTag])
    | DefFuncT b => exact mixed_pair_false dts (.DefStructT a) (.DefFuncT b) n (by simp [strTag])
  | DefArrayT a =>
    cases b with
    | DefStructT b => exact mixed_pair_false dts (.DefArrayT a) (.DefStructT b) n (by simp [strTag])
    | DefArrayT b => exact array_pair_total_of_heap dts heapMatch hheap a b n
    | DefFuncT b => exact mixed_pair_false dts (.DefArrayT a) (.DefFuncT b) n (by simp [strTag])
  | DefFuncT a =>
    cases b with
    | DefStructT b => exact mixed_pair_false dts (.DefFuncT a) (.DefStructT b) n (by simp [strTag])
    | DefArrayT b => exact mixed_pair_false dts (.DefFuncT a) (.DefArrayT b) n (by simp [strTag])
    | DefFuncT b => exact func_pair_total_of_heap dts heapMatch hheap a b n

theorem match_strtype_success_iff_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.strtype) (result : Bool) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_strtype» dts a b⟩)
      n (.success (.of result)) finish ↔
    result = strMatch heapMatch a b ∧ finish = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (match_strtype_total_of_heap dts heapMatch hheap a b n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact match_strtype_total_of_heap dts heapMatch hheap a b finish

end properties.wasm_module_ok.MatchStrtypeConditional
