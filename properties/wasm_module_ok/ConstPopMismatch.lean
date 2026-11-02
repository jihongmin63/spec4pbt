import properties.wasm_module_ok.PopGeneralValidation
import properties.wasm_module_ok.BotMatchValidation
import properties.wasm_module_ok.FiniteValidTypes

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstPopMismatch

theorem bot_pops_as_i32 (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (.NoEllipses, [.NumT .I32T]) (.NoEllipses, [.BotT])⟩)
      n (.success (.of
        (SpecTec.ellipses.NoEllipses,
          ([] : List SpecTec.valtype)))) n := by
  apply PopGeneralValidation.pop_noellipses_of_match
    c [.NumT .I32T] [.BotT] n n (by simp)
  simpa using
    (BotMatchValidation.match_resulttype_bot_list_total
      c [.NumT .I32T] n)

/-- A successful pop cannot establish exact membership of its required type
from membership of the available stack types. -/
theorem bot_pop_does_not_supply_exact_i32
    (c : SpecTec.context) (n : Nat) :
    ∃ s : Finset SpecTec.valtype,
      SpecTec.valtype.BotT ∈ s ∧
      SpecTec.valtype.NumT .I32T ∉ s ∧
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨SpecTec.inferresulttype,
          SpecTec.SpecTecCall.«$pop» c
            (.NoEllipses, [.NumT .I32T]) (.NoEllipses, [.BotT])⟩)
        n (.success (.of
          (SpecTec.ellipses.NoEllipses,
            ([] : List SpecTec.valtype)))) n := by
  exact ⟨{.BotT}, by simp, by simp, bot_pops_as_i32 c n⟩

end properties.wasm_module_ok.ConstPopMismatch
