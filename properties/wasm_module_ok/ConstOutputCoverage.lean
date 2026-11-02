import properties.wasm_module_ok.ConstBasicOutputCover
import properties.wasm_module_ok.ConstArithmeticOutputCover
import properties.wasm_module_ok.ConstStructOutputCover
import properties.wasm_module_ok.ConstArrayOutputSeed
import properties.wasm_module_ok.ConstExternOutputCover
import properties.wasm_module_ok.ConstI31Production

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstOutputCoverage

inductive Covered (c : SpecTec.context)
    (s : Finset SpecTec.valtype) (u : SpecTec.valtype) : Prop where
  | basic : u ∈ ConstBasicSeed.basicBase c → Covered c s u
  | structImplicit :
      u ∈ ConstStructImplicitProduction.structImplicitBase c → Covered c s u
  | array :
      u ∈ ConstArrayFixedZeroProduction.arrayFixedZeroBase c → Covered c s u
  | i31 : ConstI31Production.i31Step s u = true → Covered c s u
  | structExplicit :
      ConstStructExplicitProduction.structExplicitStep c s u = true →
      Covered c s u
  | externConvert :
      ConstExternConvertProduction.externTypeStep s u = true →
      Covered c s u

theorem literal_mem_basic (c : SpecTec.context) (u : SpecTec.valtype)
    (h : u ∈ ConstLiteralProduction.literalBase c) :
    u ∈ ConstBasicSeed.basicBase c := by
  exact Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_left _ h))

theorem arithmetic_mem_binop (i : SpecTec.instr)
    (h : i ∈ ConstArithmeticValidation.arithmeticOps) :
    ∃ op : SpecTec.binop_, i = .BINOP op := by
  simp only [ConstArithmeticValidation.arithmeticOps,
    List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h | h | h | h | h | h <;> exact ⟨_, h⟩

theorem covered_of_syntax
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (s : Finset SpecTec.valtype) (i : SpecTec.instr)
    (iit : SpecTec.inferinstrtype) (u : SpecTec.valtype)
    (start fin : Nat)
    (hsyntax : ConstAdditionalSyntaxValidation.Syntax c i)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt i⟩)
      start (.success (.of iit)) fin)
    (hinputs : ∀ t ∈ iit.1.INS.2, t ∈ s)
    (houts : iit.1.OUTS = (.NoEllipses, [u])) :
    Covered c s u := by
  cases hsyntax with
  | arithmetic i hm =>
    obtain ⟨op, rfl⟩ := arithmetic_mem_binop i hm
    exact .basic (literal_mem_basic c u
      (ConstArithmeticOutputCover.binop_output_in_literal_base
        c irt op iit u start fin hcall houts))
  | num v =>
    exact .basic (ConstBasicOutputCover.numeric_output_in_basic
      c irt v iit u start fin hcall houts)
  | vec v =>
    exact .basic (literal_mem_basic c u
      (ConstArithmeticOutputCover.vec_output_in_literal_base
        c irt v iit u start fin hcall houts))
  | refNull ht =>
    exact .basic (ConstBasicOutputCover.ref_null_output_in_basic
      c irt ht iit u start fin hcall houts)
  | refFunc x =>
    exact .basic (ConstBasicOutputCover.ref_func_output_in_basic
      c irt x iit u start fin hcall houts)
  | refI31 =>
    have hiit :=
      (ConstI31Dispatch.i31_instruction_effect
        c irt iit start fin hcall).1
    have hoperand : SpecTec.valtype.NumT .I32T ∈ s := by
      apply hinputs
      rw [hiit]
      simp
    exact .i31 (ConstI31Production.i31_step_of_instr_effect
      c irt s u iit start fin hoperand hcall houts)
  | structNew x op =>
    cases op with
    | Implicit =>
      exact .structImplicit
        ((ConstStructImplicitProduction.struct_implicit_base_mem_iff c u).2
          (ConstStructOutputCover.implicit_output_has_seed
            c irt x iit u start fin hcall houts))
    | Explicit =>
      exact .structExplicit
        (ConstStructOutputCover.explicit_output_has_step
          c irt x iit s u start fin hcall hinputs houts)
  | arrayNew x op =>
    cases op with
    | Implicit =>
      exact .array
        ((ConstArrayFixedZeroProduction.array_fixed_zero_base_mem_iff c u).2
          (ConstArrayOutputSeed.array_new_implicit_output_seed
            c irt x iit u start fin hcall houts))
    | Explicit =>
      exact .array
        ((ConstArrayFixedZeroProduction.array_fixed_zero_base_mem_iff c u).2
          (ConstArrayOutputSeed.array_new_explicit_output_seed
            c irt x iit u start fin hcall houts))
  | arrayNewFixed x count =>
    exact .array
      ((ConstArrayFixedZeroProduction.array_fixed_zero_base_mem_iff c u).2
        (ConstArrayOutputSeed.array_new_fixed_output_seed
          c irt x count iit u start fin hcall houts))
  | externConvert op =>
    exact .externConvert
      (ConstExternOutputCover.extern_output_has_step_of_all_inputs
        c irt op iit s u start fin hcall hinputs houts)
  | globalGet x t hget =>
    have hallowed :
        ConstSyntaxDecision.syntaxAllowed c (.«GLOBAL.GET» x) = true :=
      (ConstSyntaxDecision.syntaxAllowed_iff c _).2
        (.globalGet x t hget)
    exact .basic (ConstBasicOutputCover.global_get_output_in_basic
      c irt x iit u start fin hallowed hcall houts)

end properties.wasm_module_ok.ConstOutputCoverage
