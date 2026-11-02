import properties.wasm_module_ok.bundle.Helpers
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchFunctypeCalls

/-- The translated function match reverses parameter direction and preserves
    result direction. This decomposition does not assume either child is total. -/
theorem match_functype_success_iff_calls
    (dts : List SpecTec.deftype)
    (inputs outputs inputs' outputs' : SpecTec.resulttype)
    (n finish : Nat) (result : Bool) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool, SpecTec.Call.«$match_functype» dts
        (.FuncT inputs outputs) (.FuncT inputs' outputs')⟩)
      n (.success (.of result)) finish ↔
    ∃ middle : Nat, ∃ inputMatch outputMatch : Bool,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_resulttype» dts inputs' inputs⟩)
        n (.success (.of inputMatch)) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_resulttype» dts outputs outputs'⟩)
        middle (.success (.of outputMatch)) finish ∧
      result = (inputMatch && outputMatch) := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      obtain ⟨idx, hselected⟩ :=
        (properties.wasm_module_ok.Execution.tryClauses_success_iff
          (SpecTec.«$match_functype_clauses» dts
            (.FuncT inputs outputs) (.FuncT inputs' outputs'))
          n (.of result) finish).1 hbody
      unfold SpecTec.«$match_functype_clauses» at hselected
      cases hselected with
      | here hfirst =>
        unfold SpecTec.«$match_functype:clause:0» at hfirst
        cases hfirst with
        | bind_success hinputs htail =>
          rename_i middle inputMatch
          cases htail with
          | bind_success houtputs hpure =>
            rename_i _ outputMatch
            cases hpure
            exact ⟨middle, inputMatch, outputMatch,
              hinputs, houtputs, rfl⟩
      | next _ hnone => cases hnone
  · rintro ⟨middle, inputMatch, outputMatch,
      hinputs, houtputs, rfl⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.«$match_functype_clauses» dts
          (.FuncT inputs outputs) (.FuncT inputs' outputs')))
      n (.success (.of (inputMatch && outputMatch))) finish
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$match_functype:clause:0» dts
        (.FuncT inputs outputs) (.FuncT inputs' outputs'))
      n (.success (.of (inputMatch && outputMatch))) finish
    unfold SpecTec.«$match_functype:clause:0»
    apply SpecTecExecution.Eval.bind_success hinputs
    apply SpecTecExecution.Eval.bind_success houtputs
    exact SpecTecExecution.Eval.pure (inputMatch && outputMatch)

def matchFunctypeResult
    (resulttypeMatch : SpecTec.resulttype → SpecTec.resulttype → Bool) :
    SpecTec.functype → SpecTec.functype → Bool
  | .FuncT inputs outputs, .FuncT inputs' outputs' =>
      resulttypeMatch inputs' inputs && resulttypeMatch outputs outputs'

theorem match_functype_total_of_resulttype
    (dts : List SpecTec.deftype)
    (resulttypeMatch : SpecTec.resulttype → SpecTec.resulttype → Bool)
    (hresult : ∀ ts₁ ts₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_resulttype» dts ts₁ ts₂⟩)
        n (.success (.of (resulttypeMatch ts₁ ts₂))) n)
    (ft₁ ft₂ : SpecTec.functype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_functype» dts ft₁ ft₂⟩)
      n (.success (.of
        (matchFunctypeResult resulttypeMatch ft₁ ft₂))) n := by
  cases ft₁ with
  | FuncT inputs outputs =>
    cases ft₂ with
    | FuncT inputs' outputs' =>
      apply (match_functype_success_iff_calls
        dts inputs outputs inputs' outputs' n n
          (matchFunctypeResult resulttypeMatch
            (.FuncT inputs outputs) (.FuncT inputs' outputs'))).2
      exact ⟨n, resulttypeMatch inputs' inputs,
        resulttypeMatch outputs outputs',
        hresult inputs' inputs n, hresult outputs outputs' n, rfl⟩

theorem match_functype_success_iff_of_resulttype
    (dts : List SpecTec.deftype)
    (resulttypeMatch : SpecTec.resulttype → SpecTec.resulttype → Bool)
    (hresult : ∀ ts₁ ts₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_resulttype» dts ts₁ ts₂⟩)
        n (.success (.of (resulttypeMatch ts₁ ts₂))) n)
    (ft₁ ft₂ : SpecTec.functype) (result : Bool)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_functype» dts ft₁ ft₂⟩)
      n (.success (.of result)) finish ↔
    result = matchFunctypeResult resulttypeMatch ft₁ ft₂ ∧
      finish = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (match_functype_total_of_resulttype
          dts resulttypeMatch hresult ft₁ ft₂ n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact match_functype_total_of_resulttype
      dts resulttypeMatch hresult ft₁ ft₂ finish

end properties.wasm_module_ok.MatchFunctypeCalls
