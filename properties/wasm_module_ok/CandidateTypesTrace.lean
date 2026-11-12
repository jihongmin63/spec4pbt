import properties.wasm_module_ok.CandidateRectypeSearchExact
import properties.wasm_module_ok.TypesPrefixValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.CandidateTypesTrace

theorem type_ok_of_rectype
    (c result : SpecTec.context) (sts : List SpecTec.subtype)
    (start finish : Nat)
    (hrect : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Rectype_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Type_ok c (.RecT sts)⟩)
      start (.success (.of result)) finish := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.Type_ok_clauses c (.RecT sts)))
    start (.success (.of result)) finish
  apply SpecTecExecution.tryClauses_cons_success
  unfold SpecTec.«Type_ok:clause:0»
  apply SpecTecExecution.Eval.bind_success hrect
  exact SpecTecExecution.Eval.pure result

theorem types_ok_cons_of_calls
    (c next result : SpecTec.context)
    (t : SpecTec.type) (ts : List SpecTec.type)
    (start middle finish : Nat)
    (hhead : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Type_ok c t⟩)
      start (.success (.of next)) middle)
    (htail : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Types_ok next ts⟩)
      middle (.success (.of result)) finish) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Types_ok c (t :: ts)⟩)
      start (.success (.of result)) finish := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (.orElse (SpecTec.«Types_ok:clause:0» c (t :: ts))
      (fun _ => SpecTecExecution.tryClauses
        [SpecTec.«Types_ok:clause:1» c (t :: ts)]))
    start (.success (.of result)) finish
  apply SpecTecExecution.Eval.orElse_success
  unfold SpecTec.«Types_ok:clause:0»
  apply SpecTecExecution.Eval.bind_success
    (SpecTecExecution.Eval.guard_true (by simp))
  apply SpecTecExecution.Eval.bind_success hhead
  apply SpecTecExecution.Eval.bind_success htail
  exact SpecTecExecution.Eval.pure result

end properties.wasm_module_ok.CandidateTypesTrace
