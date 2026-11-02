import properties.wasm_module_ok.PopResult
import properties.wasm_module_ok.PushValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.StackClosure

theorem pop_push_entries_closed
    (c : SpecTec.context)
    (need outs available : List SpecTec.valtype)
    (popped pushed : SpecTec.inferresulttype)
    (start middle fin : Nat)
    (hpop : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (.NoEllipses, need) (.NoEllipses, available)⟩)
      start (.success (.of popped)) middle)
    (hpush : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$push» c
          (.NoEllipses, outs) popped⟩)
      middle (.success (.of pushed)) fin)
    (P : SpecTec.valtype → Prop)
    (havailable : ∀ t ∈ available, P t)
    (houts : ∀ t ∈ outs, P t) :
    ∀ t ∈ pushed.2, P t := by
  have hpopped := PopResult.pop_noellipses_success_result
    c need available popped start middle hpop
  subst popped
  have hpushresult := (PushValidation.push_success_iff_result
    c (.NoEllipses, outs)
      (.NoEllipses, available.take (available.length - need.length))
      pushed middle fin).1 hpush
  have hs :
      pushed = (.NoEllipses,
        available.take (available.length - need.length) ++ outs) := by
    simpa [PushValidation.pushResult] using hpushresult.1.symm
  intro t ht
  rw [hs] at ht
  rcases List.mem_append.mp ht with hprefix | hout
  · exact havailable t (List.mem_of_mem_take hprefix)
  · exact houts t hout

end properties.wasm_module_ok.StackClosure
