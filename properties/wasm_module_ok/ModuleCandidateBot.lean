import properties.wasm_module_ok.ElemDataGlobalsValidation
import properties.wasm_module_ok.Validity

set_option autoImplicit false

namespace properties.wasm_module_ok.ModuleCandidateBot

theorem trace_no_bot_candidates
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m) :
    (SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse tr.c0) ∧
    (SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse tr.c1) ∧
    (SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse tr.c2) ∧
    (SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse tr.c3) ∧
    (SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse tr.c4) ∧
    (SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse tr.c5) ∧
    (SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse tr.c6) ∧
    (SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse tr.c7) ∧
    (SpecTec.valtype.BotT ∉ FiniteValidTypes.candidateUniverse tr.c8) := by
  have hbase :=
    ConstCandidateBot.empty_context_no_bot_candidate
      tr.c tr.n1 tr.n2 tr.empty_ok
  have hbaseRef : SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse
        { tr.c with REFS := tr.free } := by
    intro hb
    obtain ⟨mutation, hm⟩ :=
      (ConstCandidateBot.bot_mem_candidate_iff
        { tr.c with REFS := tr.free }).1 hb
    exact hbase ((ConstCandidateBot.bot_mem_candidate_iff tr.c).2
      ⟨mutation, by simpa using hm⟩)
  have h0 := TypeGlobalsValidation.types_success_no_bot_candidate
    { tr.c with REFS := tr.free } tr.c0 m.TYPES
    tr.n2 tr.n3 hbaseRef tr.types_ok
  have h1 := ConstCandidateBot.imports_success_no_bot_candidate
    tr.c0 tr.c1 m.IMPORTS tr.n3 tr.n4 h0 tr.imports_ok
  have h2 := FuncGlobalsValidation.funcs_success_no_bot_candidate
    tr.c1 tr.c2 m.FUNCS tr.n4 tr.n5 h1 tr.funcs_ok
  have h3 := TableGlobalsValidation.tables_success_no_bot_candidate
    tr.c2 tr.c3 m.TABLES tr.n5 tr.n6 h2 tr.tables_ok
  have h4 := MemGlobalsValidation.mems_success_no_bot_candidate
    tr.c3 tr.c4 m.MEMS tr.n6 tr.n7 h3 tr.mems_ok
  have h5 := ConstCandidateBot.globals_success_no_bot_candidate
    tr.c4 tr.c5 m.GLOBALS tr.n7 tr.n8 h4 tr.globals_ok
  have h6 := TagGlobalsValidation.tags_success_no_bot_candidate
    tr.c5 tr.c6 m.TAGS tr.n8 tr.n9 h5 tr.tags_ok
  have h7 := ElemDataGlobalsValidation.elems_success_no_bot_candidate
    tr.c6 tr.c7 m.ELEMS tr.n9 tr.n10 h6 tr.elems_ok
  have h8 := ElemDataGlobalsValidation.datas_success_no_bot_candidate
    tr.c7 tr.c8 m.DATAS tr.n10 tr.n11 h7 tr.datas_ok
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem trace_const_target_shape
    (m : SpecTec.module) (tr : Validity.ModuleOkTrace m)
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (start fin : Nat)
    (hc : c ∈ [tr.c0, tr.c1, tr.c2, tr.c3, tr.c4,
      tr.c5, tr.c6, tr.c7, tr.c8])
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Const_ok c t xs⟩)
      start (.success (.of ())) fin) :
    (∃ a : SpecTec.numtype, t = .NumT a) ∨
      (∃ a : SpecTec.vectype, t = .VecT a) ∨
      (∃ a : SpecTec.reftype, t = .RefT a) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    trace_no_bot_candidates m tr
  have hno : SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse c := by
    simp at hc
    rcases hc with hc | hc | hc | hc | hc | hc | hc | hc | hc
    · rw [hc]; exact h0
    · rw [hc]; exact h1
    · rw [hc]; exact h2
    · rw [hc]; exact h3
    · rw [hc]; exact h4
    · rw [hc]; exact h5
    · rw [hc]; exact h6
    · rw [hc]; exact h7
    · rw [hc]; exact h8
  exact ConstTargetShape.const_ok_target_outer_shape
    c t xs start fin hno h

end properties.wasm_module_ok.ModuleCandidateBot
