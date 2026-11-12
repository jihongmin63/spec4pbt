import properties.wasm_module_ok.ConstLiteralCandidate
import properties.wasm_module_ok.ConstVectorCandidate
import properties.wasm_module_ok.ConstRefNullCandidate
import properties.wasm_module_ok.ConstRefFuncCandidate
import properties.wasm_module_ok.ConstI31Candidate
import properties.wasm_module_ok.ConstStructNewCandidate
import properties.wasm_module_ok.ConstArrayNewCandidate
import properties.wasm_module_ok.ConstArrayFixedCandidate
import properties.wasm_module_ok.ConstExternCandidate
import properties.wasm_module_ok.ConstGlobalGetCandidate
import properties.wasm_module_ok.ConstBinopCandidate
import properties.wasm_module_ok.ConstAdditionalSyntaxValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstSyntaxCandidate

theorem syntax_instruction_effect_candidate
    (base c : SpecTec.context) (i : SpecTec.instr)
    (irt : SpecTec.inferresulttype)
    (iit : SpecTec.inferinstrtype) (start fin : Nat)
    (hs : ConstAdditionalSyntaxValidation.Syntax base i)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt i⟩)
      start (.success (.of iit)) fin) :
    ∃ need outs : List SpecTec.valtype,
      iit.1.INS = (.NoEllipses, need) ∧
      iit.1.OUTS = (.NoEllipses, outs) ∧
      ∀ t ∈ outs, t ∈ FiniteValidTypes.candidateUniverse c := by
  cases hs with
  | arithmetic i hi =>
    simp only [ConstArithmeticValidation.arithmeticOps,
      List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with heq | heq | heq | heq | heq | heq <;>
      subst i <;>
      exact ConstBinopCandidate.binop_effect_candidate
        c irt _ iit start fin h
  | num v =>
    exact ConstLiteralCandidate.literal_effect_candidate
      c irt v iit start fin h
  | vec v =>
    exact ConstVectorCandidate.vector_effect_candidate
      c irt v iit start fin h
  | refNull ht =>
    exact ConstRefNullCandidate.ref_null_effect_candidate
      c irt ht iit start fin h
  | refFunc x =>
    exact ConstRefFuncCandidate.ref_func_effect_candidate
      c irt x iit start fin h
  | refI31 =>
    exact ConstI31Candidate.i31_effect_candidate
      c irt iit start fin h
  | structNew ti op =>
    cases op with
    | Implicit =>
      exact ConstStructNewCandidate.struct_new_implicit_effect_candidate
        c irt ti iit start fin h
    | Explicit =>
      exact ConstStructNewCandidate.struct_new_explicit_effect_candidate
        c irt ti iit start fin h
  | arrayNew ti op =>
    cases op with
    | Implicit =>
      exact ConstArrayNewCandidate.array_new_implicit_effect_candidate
        c irt ti iit start fin h
    | Explicit =>
      exact ConstArrayNewCandidate.array_new_explicit_effect_candidate
        c irt ti iit start fin h
  | arrayNewFixed ti count =>
    exact ConstArrayFixedCandidate.array_new_fixed_effect_candidate
      c irt ti count iit start fin h
  | externConvert op =>
    exact ConstExternCandidate.extern_convert_effect_candidate
      c irt op iit start fin h
  | globalGet x t hget =>
    exact ConstGlobalGetCandidate.global_get_effect_candidate
      c irt x iit start fin h

end properties.wasm_module_ok.ConstSyntaxCandidate
