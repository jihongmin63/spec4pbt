import properties.wasm_module_ok.ConstLiteralProduction
import properties.wasm_module_ok.ConstNumericBinopDispatch

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstArithmeticOutputCover

theorem binop_output_in_literal_base
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (op : SpecTec.binop_) (iit : SpecTec.inferinstrtype)
    (u : SpecTec.valtype) (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.BINOP op)⟩)
      start (.success (.of iit)) fin)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    u ∈ ConstLiteralProduction.literalBase c := by
  obtain ⟨nt, _, rfl⟩ :=
    (ConstNumericBinopDispatch.numeric_binop_dispatch_iff
      c irt op iit start fin).1 hcall
  have hu : u = .NumT nt := by
    simpa using houts.symm
  subst u
  exact (ConstLiteralProduction.literal_base_mem_iff c _).2 (by rfl)

theorem vec_output_in_literal_base
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (v : SpecTec.vec_) (iit : SpecTec.inferinstrtype)
    (u : SpecTec.valtype) (start fin : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt (.«VEC.CONST» v)⟩)
      start (.success (.of iit)) fin)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    u ∈ ConstLiteralProduction.literalBase c := by
  obtain ⟨rfl, _⟩ :=
    ConstVectorDispatch.vec_literal_effect c irt v iit start fin hcall
  have hu : u = .VecT .V128T := by
    simpa using houts.symm
  subst u
  exact (ConstLiteralProduction.literal_base_mem_iff c _).2 (by rfl)

end properties.wasm_module_ok.ConstArithmeticOutputCover
