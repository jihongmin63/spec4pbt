import properties.wasm_module_ok.ConstOutputCoverage
import properties.wasm_module_ok.ConstFieldCandidate

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstInputCoverage

theorem inputs_candidate_of_syntax
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (start finish : Nat)
    (hsyntax : ConstAdditionalSyntaxValidation.Syntax c i)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt i⟩)
      start (.success (.of iit)) finish) :
    ∀ t ∈ iit.1.INS.2,
      t ∈ ConstFieldCandidate.extendedCandidateUniverse c := by
  cases hsyntax with
  | arithmetic i hm =>
    obtain ⟨op, rfl⟩ := ConstOutputCoverage.arithmetic_mem_binop i hm
    intro t ht
    exact ConstFieldCandidate.old_candidate_mem_extended c t
      (ConstBasicInputCandidate.binop_inputs_candidate
        c irt op iit start finish hcall t ht)
  | num v =>
    obtain ⟨hiit, _⟩ :=
      ConstLiteralDispatch.const_literal_effect c irt v iit start finish hcall
    intro t ht
    rw [hiit] at ht
    cases ht
  | vec v =>
    intro t ht
    exact ConstFieldCandidate.old_candidate_mem_extended c t
      (ConstBasicInputCandidate.vec_const_inputs_candidate
        c irt v iit start finish hcall t ht)
  | refNull ht =>
    obtain ⟨_, hiit, _⟩ :=
      (ConstRefNullDispatch.ref_null_dispatch_iff
        c irt ht iit start finish).1 hcall
    intro t hmem
    rw [hiit] at hmem
    cases hmem
  | refFunc x =>
    obtain ⟨dt, _, _, hiit, _⟩ :=
      (ConstRefFuncEffect.ref_func_instruction_iff
        c irt x iit start finish).1 hcall
    intro t ht
    rw [hiit] at ht
    cases ht
  | refI31 =>
    intro t ht
    exact ConstFieldCandidate.old_candidate_mem_extended c t
      (ConstBasicInputCandidate.ref_i31_inputs_candidate
        c irt iit start finish hcall t ht)
  | structNew x op =>
    cases op with
    | Implicit =>
      obtain ⟨fields, dt, middle, hstruct, hdefault, hget, hiit⟩ :=
        (ConstStructImplicitDispatch.struct_new_implicit_dispatch_iff
          c irt x iit start finish).1 hcall
      intro t ht
      rw [hiit] at ht
      cases ht
    | Explicit =>
      exact ConstFieldCandidate.struct_new_explicit_inputs_extended
        c irt x iit start finish hcall
  | arrayNew x op =>
    cases op with
    | Implicit =>
      exact ConstFieldCandidate.array_new_implicit_inputs_extended
        c irt x iit start finish hcall
    | Explicit =>
      exact ConstFieldCandidate.array_new_explicit_inputs_extended
        c irt x iit start finish hcall
  | arrayNewFixed x count =>
    exact ConstFieldCandidate.array_new_fixed_inputs_extended
      c irt x count iit start finish hcall
  | externConvert op =>
    intro t ht
    exact ConstFieldCandidate.old_candidate_mem_extended c t
      (ConstBasicInputCandidate.extern_convert_inputs_candidate
        c irt op iit start finish hcall t ht)
  | globalGet x t hget =>
    have hallowed :
        ConstSyntaxDecision.syntaxAllowed c (.«GLOBAL.GET» x) = true :=
      (ConstSyntaxDecision.syntaxAllowed_iff c _).2
        (.globalGet x t hget)
    obtain ⟨actual, hglobal, hiit, _⟩ :=
      (ConstGlobalGetCombined.global_get_constant_instruction_iff
        c irt x iit start finish).1 ⟨hallowed, hcall⟩
    intro t ht
    rw [hiit] at ht
    cases ht

theorem inputs_candidate_of_is_const
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (start middle finish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$is_const» c i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt i⟩)
      middle (.success (.of iit)) finish) :
    ∀ t ∈ iit.1.INS.2,
      t ∈ ConstFieldCandidate.extendedCandidateUniverse c := by
  have hsyntax :=
    (ConstSyntaxClassification.is_const_success_iff
      c i start middle).1 hconst |>.1
  exact inputs_candidate_of_syntax c irt i iit middle finish hsyntax hcall

end properties.wasm_module_ok.ConstInputCoverage
