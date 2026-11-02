import properties.wasm_module_ok.ConstRefFuncEffect
import properties.wasm_module_ok.ConstSyntaxDecision

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstRefFuncCombined

theorem ref_func_constant_instruction_iff
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.funcidx) (iit : SpecTec.inferinstrtype)
    (n fin : Nat) :
    ConstSyntaxDecision.syntaxAllowed c (.«REF.FUNC» x) = true ∧
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«REF.FUNC» x)⟩)
      n (.success (.of iit)) fin ↔
    ∃ dt : SpecTec.deftype,
      c.FUNCS[x]? = some dt ∧
      FreeUnionValidation.HasFunc c.REFS x ∧
      iit =
        (⟨{ INS := (.NoEllipses, []),
             OUTS := (.NoEllipses,
               [.RefT (.«% %» .NoNull (.DefHT dt))]) },
          ([] : List SpecTec.localidx)⟩ : SpecTec.inferinstrtype) ∧
      fin = n := by
  constructor
  · rintro ⟨_, hcall⟩
    exact (ConstRefFuncEffect.ref_func_instruction_iff
      c irt x iit n fin).1 hcall
  · intro h
    constructor
    · exact (ConstSyntaxDecision.syntaxAllowed_iff c (.«REF.FUNC» x)).2
        (.refFunc x)
    · exact (ConstRefFuncEffect.ref_func_instruction_iff
        c irt x iit n fin).2 h

end properties.wasm_module_ok.ConstRefFuncCombined
