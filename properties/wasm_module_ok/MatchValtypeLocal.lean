import properties.wasm_module_ok.MatchValtypeConditional
import properties.wasm_module_ok.MatchReftypeLocal
import properties.wasm_module_ok.ReadyMatchReachability

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchValtypeLocal

def refHeap : SpecTec.reftype → SpecTec.heaptype
  | .«% %» _ ht => ht

theorem match_valtype_ref_ref_pair_total
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (a b : SpecTec.reftype) (n : Nat)
    (hheap : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype»
        dts (refHeap a) (refHeap b)⟩)
      n (.success (.of (heapMatch (refHeap a) (refHeap b)))) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype»
        dts (.RefT a) (.RefT b)⟩)
      n (.success (.of
        (MatchReftypeConditional.matchReftypeResult heapMatch a b))) n := by
  cases a with
  | «% %» n1 h1 =>
    cases b with
    | «% %» n2 h2 =>
      let a : SpecTec.reftype := SpecTec.reftype.«% %» n1 h1
      let b : SpecTec.reftype := SpecTec.reftype.«% %» n2 h2
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$match_valtype_clauses» dts (.RefT a) (.RefT b)) ())
        n (.success (.of
          (MatchReftypeConditional.matchReftypeResult heapMatch a b))) n
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · change SpecTecExecution.Eval SpecTec.specTecProgram
          (SpecTec.«$match_valtype:clause:0» dts (.RefT a) (.RefT b))
          n .unmatch n
        unfold SpecTec.«$match_valtype:clause:0»
        exact SpecTecExecution.Eval.bind_unmatch
          (SpecTecExecution.Eval.guard_false
            (by simp [SpecTec.«exec:match:valtype:NumT»]))
      · apply SpecTecExecution.firstSuccess_cons_unmatch
        · change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_valtype:clause:1» dts (.RefT a) (.RefT b))
            n .unmatch n
          unfold SpecTec.«$match_valtype:clause:1»
          exact SpecTecExecution.Eval.bind_unmatch
            (SpecTecExecution.Eval.guard_false
              (by simp [SpecTec.«exec:match:valtype:VecT»]))
        · apply SpecTecExecution.firstSuccess_cons_success
          change SpecTecExecution.Eval SpecTec.specTecProgram
            (SpecTec.«$match_valtype:clause:2» dts (.RefT a) (.RefT b))
            n (.success (.of
              (MatchReftypeConditional.matchReftypeResult heapMatch a b))) n
          unfold SpecTec.«$match_valtype:clause:2»
          apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true rfl
          · apply SpecTecExecution.Eval.bind_success
            · exact SpecTecExecution.Eval.guard_true rfl
            · apply SpecTecExecution.Eval.bind_success
              · exact MatchReftypeLocal.match_reftype_pair_total
                  dts heapMatch n1 n2 h1 h2 n (by
                    simpa [refHeap] using hheap)
              · exact SpecTecExecution.Eval.pure
                  (MatchReftypeConditional.matchReftypeResult heapMatch a b)

theorem match_valtype_total_of_local_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (u t : SpecTec.valtype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceValHeaptypes u →
      h2 ∈ ReadyMatchReachability.sourceValHeaptypes t →
      ∀ supply, SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        supply (.success (.of (heapMatch h1 h2))) supply) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» dts u t⟩)
      n (.success (.of
        (MatchValtypeConditional.matchValtypeResult heapMatch u t))) n := by
  cases u with
  | NumT a =>
    cases t with
    | NumT b => exact MatchValtypeBasic.match_valtype_num_total dts a b n
    | VecT b => exact MatchValtypeBasic.match_valtype_num_vec_total dts a b n
    | RefT b => exact MatchValtypeBasic.match_valtype_num_ref_total dts a b n
    | BotT => exact MatchValtypeBasic.match_valtype_num_bot_total dts a n
  | VecT a =>
    cases t with
    | NumT b => exact MatchValtypeBasic.match_valtype_vec_num_total dts a b n
    | VecT b => exact MatchValtypeBasic.match_valtype_vec_total dts a b n
    | RefT b => exact MatchValtypeBasic.match_valtype_vec_ref_total dts a b n
    | BotT => exact MatchValtypeBasic.match_valtype_vec_bot_total dts a n
  | RefT a =>
    cases t with
    | NumT b => exact MatchValtypeBasic.match_valtype_ref_num_total dts a b n
    | VecT b => exact MatchValtypeBasic.match_valtype_ref_vec_total dts a b n
    | RefT b =>
      apply match_valtype_ref_ref_pair_total dts heapMatch a b n
      apply hheap (refHeap a) (refHeap b)
      · cases a with
        | «% %» _ ht => simp [refHeap, ReadyMatchReachability.sourceValHeaptypes]
      · cases b with
        | «% %» _ ht => simp [refHeap, ReadyMatchReachability.sourceValHeaptypes]
    | BotT => exact MatchValtypeBasic.match_valtype_ref_bot_total dts a n
  | BotT => exact MatchValtypeBasic.match_valtype_bot_total dts t n

theorem match_valtype_total_of_local_heap_at
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (u t : SpecTec.valtype) (n : Nat)
    (hheap : ∀ h1 h2,
      h1 ∈ ReadyMatchReachability.sourceValHeaptypes u →
      h2 ∈ ReadyMatchReachability.sourceValHeaptypes t →
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool, SpecTec.SpecTecCall.«$match_heaptype» dts h1 h2⟩)
        n (.success (.of (heapMatch h1 h2))) n) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype» dts u t⟩)
      n (.success (.of
        (MatchValtypeConditional.matchValtypeResult heapMatch u t))) n := by
  cases u with
  | NumT a =>
    cases t with
    | NumT b => exact MatchValtypeBasic.match_valtype_num_total dts a b n
    | VecT b => exact MatchValtypeBasic.match_valtype_num_vec_total dts a b n
    | RefT b => exact MatchValtypeBasic.match_valtype_num_ref_total dts a b n
    | BotT => exact MatchValtypeBasic.match_valtype_num_bot_total dts a n
  | VecT a =>
    cases t with
    | NumT b => exact MatchValtypeBasic.match_valtype_vec_num_total dts a b n
    | VecT b => exact MatchValtypeBasic.match_valtype_vec_total dts a b n
    | RefT b => exact MatchValtypeBasic.match_valtype_vec_ref_total dts a b n
    | BotT => exact MatchValtypeBasic.match_valtype_vec_bot_total dts a n
  | RefT a =>
    cases t with
    | NumT b => exact MatchValtypeBasic.match_valtype_ref_num_total dts a b n
    | VecT b => exact MatchValtypeBasic.match_valtype_ref_vec_total dts a b n
    | RefT b =>
      apply match_valtype_ref_ref_pair_total dts heapMatch a b n
      apply hheap (refHeap a) (refHeap b)
      · cases a with
        | «% %» _ ht => simp [refHeap, ReadyMatchReachability.sourceValHeaptypes]
      · cases b with
        | «% %» _ ht => simp [refHeap, ReadyMatchReachability.sourceValHeaptypes]
    | BotT => exact MatchValtypeBasic.match_valtype_ref_bot_total dts a n
  | BotT => exact MatchValtypeBasic.match_valtype_bot_total dts t n
end properties.wasm_module_ok.MatchValtypeLocal
