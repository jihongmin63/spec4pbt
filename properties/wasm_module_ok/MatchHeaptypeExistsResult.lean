import properties.wasm_module_ok.MatchHeaptypeBasic
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchHeaptypeExistsResult

theorem match_heaptype_exists_result_of_head_classifier
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (hts : List SpecTec.heaptype) (f : SpecTec.heaptype → Bool)
    (start : Nat)
    (hhead : ∀ h ∈ hts,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h (.DefHT dt)⟩)
        start (.success (.of (f h))) start) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_heaptype_exists» dts hts dt⟩)
      start (.success (.of (hts.any f))) start := by
  induction hts with
  | nil =>
      simpa using MatchHeaptypeBasic.match_heaptype_exists_nil_total dts dt start
  | cons h tl ih =>
      have hh := hhead h (by simp)
      have htail : ∀ h' ∈ tl,
          SpecTecExecution.Eval SpecTec.Body
            (.call ⟨Bool,
              SpecTec.Call.«$match_heaptype» dts h' (.DefHT dt)⟩)
            start (.success (.of (f h'))) start := by
        intro h' hm
        exact hhead h' (by simp [hm])
      cases hf : f h with
      | true =>
          simpa [List.any, hf] using
            (MatchHeaptypeBasic.match_heaptype_exists_cons_true_total
              dts h tl dt start (by simpa [hf] using hh))
      | false =>
          have hrest := ih htail
          simpa [List.any, hf] using
            (MatchHeaptypeBasic.match_heaptype_exists_cons_false_total_of_tail
              dts h tl dt (tl.any f) start (by simpa [hf] using hh) hrest)

theorem match_heaptype_exists_result_iff_of_head_classifier
    (dts : List SpecTec.deftype) (dt : SpecTec.deftype)
    (hts : List SpecTec.heaptype) (f : SpecTec.heaptype → Bool)
    (start : Nat)
    (hhead : ∀ h ∈ hts,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h (.DefHT dt)⟩)
        start (.success (.of (f h))) start)
    (result : Bool) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_heaptype_exists» dts hts dt⟩)
      start (.success (.of result)) start ↔
    result = hts.any f := by
  constructor
  · intro h
    obtain ⟨hout, _⟩ := properties.wasm_module_ok.Execution.eval_deterministic h
      (match_heaptype_exists_result_of_head_classifier
        dts dt hts f start hhead)
    cases hout
    rfl
  · intro heq
    subst result
    exact match_heaptype_exists_result_of_head_classifier
      dts dt hts f start hhead

end properties.wasm_module_ok.MatchHeaptypeExistsResult
