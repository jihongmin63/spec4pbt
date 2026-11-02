import properties.wasm_module_ok.TypeGlobalsValidation
import properties.wasm_module_ok.FuncsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.FuncGlobalsValidation

theorem func_decl_result_globals
    (c out : SpecTec.context) (f : SpecTec.func)
    (h : FuncDeclValidation.funcDeclResult c f = some out) :
    out.GLOBALS = c.GLOBALS := by
  cases hget : c.TYPES[f.FTYPE]? with
  | none => simp [FuncDeclValidation.funcDeclResult, hget] at h
  | some dt =>
      cases hft : UnrollInterface.deftypeFunctype dt with
      | none =>
          simp [FuncDeclValidation.funcDeclResult, hget, hft] at h
      | some ft =>
          simp [FuncDeclValidation.funcDeclResult, hget, hft] at h
          cases h
          rfl

theorem funcs_result_globals
    (c out : SpecTec.context) (fs : List SpecTec.func)
    (h : FuncsValidation.funcsResult c fs = some out) :
    out.GLOBALS = c.GLOBALS := by
  induction fs generalizing c out with
  | nil =>
      simp [FuncsValidation.funcsResult] at h
      cases h
      rfl
  | cons f fs ih =>
      cases hhead : FuncDeclValidation.funcDeclResult c f with
      | none =>
          simp [FuncsValidation.funcsResult, hhead] at h
      | some c₁ =>
          have htail : FuncsValidation.funcsResult c₁ fs = some out := by
            simpa [FuncsValidation.funcsResult, hhead] using h
          exact (ih c₁ out htail).trans
            (func_decl_result_globals c c₁ f hhead)

theorem funcs_success_no_bot_candidate
    (c out : SpecTec.context) (fs : List SpecTec.func)
    (start fin : Nat)
    (hinput : SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse c)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Funcs_ok c fs⟩)
      start (.success (.of out)) fin) :
    SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse out := by
  have hresult :=
    (FuncsValidation.funcs_success_iff_result
      c fs out start fin).1 h |>.1
  intro hb
  obtain ⟨m, hm⟩ := (ConstCandidateBot.bot_mem_candidate_iff out).1 hb
  rw [funcs_result_globals c out fs hresult] at hm
  exact hinput ((ConstCandidateBot.bot_mem_candidate_iff c).2 ⟨m, hm⟩)

end properties.wasm_module_ok.FuncGlobalsValidation
