import properties.wasm_module_ok.TableGlobalsValidation
import properties.wasm_module_ok.MemsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.MemGlobalsValidation

theorem mem_decl_result_globals
    (c out : SpecTec.context) (m : SpecTec.memory)
    (h : MemsValidation.memDeclResult c m = some out) :
    out.GLOBALS = c.GLOBALS := by
  cases hv : MemtypeValidation.memtypeValid m.MTYPE with
  | true =>
      simp [MemsValidation.memDeclResult, hv] at h
      cases h
      rfl
  | false =>
      simp [MemsValidation.memDeclResult, hv] at h

theorem mems_result_globals
    (c out : SpecTec.context) (ms : List SpecTec.memory)
    (h : MemsValidation.memsResult c ms = some out) :
    out.GLOBALS = c.GLOBALS := by
  induction ms generalizing c out with
  | nil =>
      simp [MemsValidation.memsResult] at h
      cases h
      rfl
  | cons m ms ih =>
      cases hhead : MemsValidation.memDeclResult c m with
      | none =>
          simp [MemsValidation.memsResult, hhead] at h
      | some c₁ =>
          have htail : MemsValidation.memsResult c₁ ms = some out := by
            simpa [MemsValidation.memsResult, hhead] using h
          exact (ih c₁ out htail).trans
            (mem_decl_result_globals c c₁ m hhead)

theorem mems_success_no_bot_candidate
    (c out : SpecTec.context) (ms : List SpecTec.memory)
    (start fin : Nat)
    (hinput : SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse c)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context,
        SpecTec.SpecTecCall.Mems_ok c ms⟩)
      start (.success (.of out)) fin) :
    SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse out := by
  have hresult :=
    (MemsValidation.mems_success_iff_result
      c ms out start fin).1 h |>.1
  intro hb
  obtain ⟨mutation, hm⟩ :=
    (ConstCandidateBot.bot_mem_candidate_iff out).1 hb
  rw [mems_result_globals c out ms hresult] at hm
  exact hinput
    ((ConstCandidateBot.bot_mem_candidate_iff c).2 ⟨mutation, hm⟩)

end properties.wasm_module_ok.MemGlobalsValidation
