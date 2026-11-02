import properties.wasm_module_ok.MatchFieldConditional

set_option autoImplicit false

namespace properties.wasm_module_ok.MatchArrayConditional

def arrayMatch (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool) :
    SpecTec.arraytype → SpecTec.arraytype → Bool
  | .ArrayT a, .ArrayT b => MatchFieldConditional.fieldMatch heapMatch a b

theorem match_array_total_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.arraytype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_arraytype» dts a b⟩)
      n (.success (.of (arrayMatch heapMatch a b))) n := by
  cases a with
  | ArrayT a =>
    cases b with
    | ArrayT b =>
      apply SpecTecExecution.Eval.call
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTecExecution.firstSuccess
          (SpecTec.«$match_arraytype_clauses» dts
            (.ArrayT a) (.ArrayT b)) ())
        n (.success (.of (arrayMatch heapMatch (.ArrayT a) (.ArrayT b)))) n
      apply SpecTecExecution.firstSuccess_cons_success
      change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$match_arraytype:clause:0» dts
          (.ArrayT a) (.ArrayT b))
        n (.success (.of (arrayMatch heapMatch (.ArrayT a) (.ArrayT b)))) n
      unfold SpecTec.«$match_arraytype:clause:0»
      apply SpecTecExecution.Eval.bind_success
      · exact MatchFieldConditional.match_field_total_of_heap
          dts heapMatch hheap a b n
      · exact SpecTecExecution.Eval.pure
          (arrayMatch heapMatch (.ArrayT a) (.ArrayT b))

theorem match_array_success_iff_of_heap
    (dts : List SpecTec.deftype)
    (heapMatch : SpecTec.heaptype → SpecTec.heaptype → Bool)
    (hheap : ∀ h₁ h₂ n,
      SpecTecExecution.Eval SpecTec.specTecProgram
        (.call ⟨Bool,
          SpecTec.SpecTecCall.«$match_heaptype» dts h₁ h₂⟩)
        n (.success (.of (heapMatch h₁ h₂))) n)
    (a b : SpecTec.arraytype) (result : Bool) (n finish : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_arraytype» dts a b⟩)
      n (.success (.of result)) finish ↔
    result = arrayMatch heapMatch a b ∧ finish = n := by
  constructor
  · intro h
    have hdet : SpecTecExecution.PrimitiveDeterministic SpecTec.specTecProgram := by
      intro request x y hp
      cases hp
    obtain ⟨hout, hsupply⟩ :=
      SpecTecExecution.eval_deterministic hdet h
        (match_array_total_of_heap dts heapMatch hheap a b n)
    cases hout
    exact ⟨rfl, hsupply⟩
  · rintro ⟨rfl, rfl⟩
    exact match_array_total_of_heap dts heapMatch hheap a b finish

end properties.wasm_module_ok.MatchArrayConditional
