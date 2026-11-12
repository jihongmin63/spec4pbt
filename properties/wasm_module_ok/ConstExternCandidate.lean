import properties.wasm_module_ok.ConstExternConvertDispatch
import properties.wasm_module_ok.FiniteValidTypes
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExternCandidate

theorem type_externop_output
    (op : SpecTec.externop_) (ht1 ht2 : SpecTec.heaptype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.heaptype × SpecTec.heaptype,
        SpecTec.Call.«$type_externop» op⟩)
      start (.success (.of (ht1, ht2))) fin) :
    ht2 = .AnyHT ∨ ht2 = .ExternHT := by
  cases h with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (.orElse (SpecTec.«$type_externop:clause:0» op)
        (fun _ => SpecTecExecution.tryClauses
          [SpecTec.«$type_externop:clause:1» op]))
      start (.success (.of (ht1, ht2))) fin at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«$type_externop:clause:0» at hfirst
      cases hfirst with
      | bind_success _ hpure =>
        cases hpure with
        | pure => exact Or.inl rfl
    | orElse_unmatch hfailedSupply hrest =>
      restore_supply hfailedSupply at hrest
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«$type_externop:clause:1» op)
          (fun _ => .unmatch))
        start (.success (.of (ht1, ht2))) fin at hrest
      cases hrest with
      | orElse_success hsecond =>
        unfold SpecTec.«$type_externop:clause:1» at hsecond
        cases hsecond with
        | bind_success _ hpure =>
          cases hpure with
          | pure => exact Or.inr rfl
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem extern_convert_effect_candidate
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.externop_) (iit : SpecTec.inferinstrtype)
    (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«EXTERN.CONVERT» op)⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  obtain ⟨ht1, ht2, nu, ht, middle, htype, _, heffect⟩ :=
    (ConstExternConvertDispatch.extern_convert_dispatch_iff
      c irt op iit start fin).1 h
  have hheap : HeaptypeValidation.heaptypeValid c ht2 = true := by
    rcases type_externop_output op ht1 ht2 start middle htype with h | h
    · subst ht2
      rfl
    · subst ht2
      rfl
  have hvalid : ValtypeValidation.valtypeValid c
      (.RefT (.«% %» nu ht2)) = true := hheap
  have hmember := FiniteValidTypes.valid_mem_candidateUniverse
    c (.RefT (.«% %» nu ht2)) hvalid
  refine ⟨[.RefT (.«% %» nu ht1)],
    [.RefT (.«% %» nu ht2)], ?_, ?_, ?_⟩
  · rw [heffect]
  · rw [heffect]
  · simpa using hmember

end properties.wasm_module_ok.ConstExternCandidate
