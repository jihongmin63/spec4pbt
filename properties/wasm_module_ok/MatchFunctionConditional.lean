import properties.wasm_module_ok.MatchResulttypeConditional
import properties.wasm_module_ok.MatchFunctypeCalls

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchFunctionConditional

def valMatch
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool) :
    SpecTec.valtype → SpecTec.valtype → Bool :=
  MatchValtypeConditional.matchValtypeResult heapMatch

def resultMatch
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool) :
    SpecTec.resulttype → SpecTec.resulttype → Bool :=
  MatchResulttypeConditional.matchResulttypeResult (valMatch heapMatch)

def functionMatch
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool) :
    SpecTec.functype → SpecTec.functype → Bool :=
  MatchFunctypeCalls.matchFunctypeResult (resultMatch heapMatch)

theorem resulttype_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (ts₁ ts₂ : SpecTec.resulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_resulttype» dts ts₁ ts₂⟩)
      n (.success (.of (resultMatch heapMatch ts₁ ts₂))) n := by
  exact MatchResulttypeConditional.match_resulttype_total_of_valtype
    dts (valMatch heapMatch)
    (MatchValtypeConditional.match_valtype_total_of_heap
      dts heapMatch hheap)
    ts₁ ts₂ n

theorem functype_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (ft₁ ft₂ : SpecTec.functype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_functype» dts ft₁ ft₂⟩)
      n (.success (.of (functionMatch heapMatch ft₁ ft₂))) n := by
  exact MatchFunctypeCalls.match_functype_total_of_resulttype
    dts (resultMatch heapMatch)
    (resulttype_total_of_heap dts heapMatch hheap)
    ft₁ ft₂ n

theorem functype_success_iff_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Bool,
          SpecTec.Call.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (ft₁ ft₂ : SpecTec.functype) (result : Bool)
    (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Bool,
        SpecTec.Call.«$match_functype» dts ft₁ ft₂⟩)
      n (.success (.of result)) finish ↔
    result = functionMatch heapMatch ft₁ ft₂ ∧ finish = n := by
  exact MatchFunctypeCalls.match_functype_success_iff_of_resulttype
    dts (resultMatch heapMatch)
    (resulttype_total_of_heap dts heapMatch hheap)
    ft₁ ft₂ result n finish

end properties.wasm_module_ok.MatchFunctionConditional
