import properties.wasm_module_ok.MatchValtypeBasic
import properties.wasm_module_ok.MatchReftypeConditional
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchValtypeConditional

def matchValtypeResult (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool) :
    SpecTec.valtype → SpecTec.valtype → Bool
  | .NumT a, .NumT b => decide (b = a)
  | .VecT a, .VecT b => decide (a = b)
  | .RefT a, .RefT b =>
      MatchReftypeConditional.matchReftypeResult heapMatch a b
  | .BotT, _ => true
  | _, _ => false

theorem match_valtype_ref_ref_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h1 h2 n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (a b : SpecTec.reftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts (.RefT a) (.RefT b)⟩)
      n (.success (.of
        (MatchReftypeConditional.matchReftypeResult heapMatch a b))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$match_valtype_clauses» dts (.RefT a) (.RefT b)))
    n (.success (.of
      (MatchReftypeConditional.matchReftypeResult heapMatch a b))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_valtype:clause:0» dts (.RefT a) (.RefT b))
      n .unmatch n
    unfold SpecTec.«$match_valtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:valtype:NumT»]))
  · apply SpecTecExecution.tryClauses_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_valtype:clause:1» dts (.RefT a) (.RefT b))
        n .unmatch n
      unfold SpecTec.«$match_valtype:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false
          (by simp [SpecTec.«exec:match:valtype:VecT»]))
    · apply SpecTecExecution.tryClauses_cons_success
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTec.«$match_valtype:clause:2» dts (.RefT a) (.RefT b))
        n (.success (.of
          (MatchReftypeConditional.matchReftypeResult heapMatch a b))) n
      unfold SpecTec.«$match_valtype:clause:2»
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true rfl
        · apply SpecTecExecution.Eval.bind_success
          · exact MatchReftypeConditional.match_reftype_total_of_heap
              dts heapMatch hheap a b n
          · exact SpecTecExecution.Eval.pure
              (MatchReftypeConditional.matchReftypeResult heapMatch a b)

theorem match_valtype_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h1 h2 n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (u t : SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts u t⟩)
      n (.success (.of (matchValtypeResult heapMatch u t))) n := by
  cases u with
  | NumT a =>
    cases t with
    | NumT b =>
      exact MatchValtypeBasic.match_valtype_num_total dts a b n
    | VecT b =>
      exact MatchValtypeBasic.match_valtype_num_vec_total dts a b n
    | RefT b =>
      exact MatchValtypeBasic.match_valtype_num_ref_total dts a b n
    | BotT =>
      exact MatchValtypeBasic.match_valtype_num_bot_total dts a n
  | VecT a =>
    cases t with
    | NumT b =>
      exact MatchValtypeBasic.match_valtype_vec_num_total dts a b n
    | VecT b =>
      exact MatchValtypeBasic.match_valtype_vec_total dts a b n
    | RefT b =>
      exact MatchValtypeBasic.match_valtype_vec_ref_total dts a b n
    | BotT =>
      exact MatchValtypeBasic.match_valtype_vec_bot_total dts a n
  | RefT a =>
    cases t with
    | NumT b =>
      exact MatchValtypeBasic.match_valtype_ref_num_total dts a b n
    | VecT b =>
      exact MatchValtypeBasic.match_valtype_ref_vec_total dts a b n
    | RefT b =>
      exact match_valtype_ref_ref_total_of_heap dts heapMatch hheap a b n
    | BotT =>
      exact MatchValtypeBasic.match_valtype_ref_bot_total dts a n
  | BotT =>
    exact MatchValtypeBasic.match_valtype_bot_total dts t n

theorem match_valtype_success_iff_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h1 h2 n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool, SpecTec.Call.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n)
    (u t : SpecTec.valtype) (result : Bool) (n fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_valtype» dts u t⟩)
      n (.success (.of result)) fin ↔
    result = matchValtypeResult heapMatch u t ∧ fin = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (match_valtype_total_of_heap dts heapMatch hheap u t n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact match_valtype_total_of_heap dts heapMatch hheap u t fin

end properties.wasm_module_ok.MatchValtypeConditional
