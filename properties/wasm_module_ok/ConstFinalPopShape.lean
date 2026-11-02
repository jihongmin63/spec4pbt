import properties.wasm_module_ok.PopResult

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstFinalPopShape

theorem final_const_pop_singleton
    (c : SpecTec.context) (t : SpecTec.valtype)
    (stack : List SpecTec.valtype)
    (ellipses : SpecTec.ellipses) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.SpecTecCall.«$pop» c
          (.NoEllipses, [t]) (.NoEllipses, stack)⟩)
      start (.success (.of
        (ellipses, ([] : List SpecTec.valtype)))) fin) :
    ∃ u : SpecTec.valtype,
      stack = [u] ∧ ellipses = .NoEllipses := by
  have hlen := PopLength.pop_noellipses_success_requires_length
    c [t] stack (ellipses, []) start fin h
  have hp := PopResult.pop_noellipses_success_result
    c [t] stack (ellipses, []) start fin h
  have hell : ellipses = .NoEllipses :=
    congrArg Prod.fst hp
  have htake : stack.take (stack.length - 1) = [] :=
    (congrArg Prod.snd hp).symm
  have htakeLength : (stack.take (stack.length - 1)).length = 0 := by
    rw [htake]
    rfl
  rw [List.length_take] at htakeLength
  have hlength : stack.length = 1 := by
    simp only [List.length_cons, List.length_nil] at hlen
    omega
  obtain ⟨u, hstack⟩ := List.length_eq_one_iff.mp hlength
  exact ⟨u, hstack, hell⟩

end properties.wasm_module_ok.ConstFinalPopShape
