import properties.wasm_module_ok.ConstStepTrace
import properties.wasm_module_ok.ConstNumericBinopDispatch
import properties.wasm_module_ok.PopNumericPair

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstBinopHead

theorem numeric_binop_cannot_head_const
    (c : SpecTec.context) (t : SpecTec.valtype)
    (op : SpecTec.binop_) (rest : List SpecTec.instr)
    (start fin : Nat) :
    ¬ SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.Const_ok c t ((.BINOP op) :: rest)⟩)
      start (.success (.of ())) fin := by
  intro h
  obtain ⟨_, _, iit, _, popped, _, _, _, _,
    middle₁, middle₂, middle₃, _, _,
    hinstr, _, hpop, _, _, _⟩ :=
    (ConstStepTrace.const_ok_cons_success_iff
      c t (.BINOP op) rest start fin).1 h
  obtain ⟨nt, _, hiit⟩ :=
    (ConstNumericBinopDispatch.numeric_binop_dispatch_iff
      c (.NoEllipses, []) op iit start middle₁).1 hinstr
  subst iit
  exact PopNumericPair.pop_numeric_pair_from_empty_impossible
    c nt popped middle₂ middle₃ (by simpa using hpop)

end properties.wasm_module_ok.ConstBinopHead
