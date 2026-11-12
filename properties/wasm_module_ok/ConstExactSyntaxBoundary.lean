import properties.wasm_module_ok.ConstSyntaxListClassification
import properties.wasm_module_ok.BlockTrace
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExactSyntaxBoundary

theorem const_ok_success_iff
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (n fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Const_ok c t xs⟩)
      n (.success (.of ())) fin ↔
    (∀ i ∈ xs, ConstAdditionalSyntaxValidation.Syntax c i) ∧
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Block_ok c
        (.InstrT [] [t] []) xs⟩)
      n (.success (.of ())) fin := by
  constructor
  · intro hcall
    cases hcall with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Const_ok:clause:0» c t xs)
          (fun _ => .unmatch))
        n (.success (.of ())) fin at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«Const_ok:clause:0» at hclause
        cases hclause with
        | bind_success hiter htail =>
          obtain ⟨hall, hmiddle⟩ :=
            (ConstSyntaxListClassification.iter_success_iff
              c xs n _).1 hiter
          subst hmiddle
          cases htail with
          | bind_success hblock hpure =>
            cases hpure
            exact ⟨hall, hblock⟩
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  · rintro ⟨hall, hblock⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Const_ok_clauses c t xs))
      n (.success (.of ())) fin
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Const_ok:clause:0» c t xs)
      n (.success (.of ())) fin
    unfold SpecTec.«Const_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success
      (ConstAdditionalSyntaxValidation.syntax_iter_total c xs n hall)
    apply SpecTecExecution.Eval.bind_success hblock
    exact SpecTecExecution.Eval.pure ()

theorem const_ok_trace_iff
    (c : SpecTec.context) (t : SpecTec.valtype)
    (xs : SpecTec.const) (n fin : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Const_ok c t xs⟩)
      n (.success (.of ())) fin ↔
    (∀ i ∈ xs, ConstAdditionalSyntaxValidation.Syntax c i) ∧
    ∃ (irt : SpecTec.inferresulttype) (indices : List SpecTec.idx)
      (ellipses : SpecTec.ellipses) (middle : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.Call.Instrs_ok c
            (.NoEllipses, []) xs⟩)
        n (.success (.of (irt, indices))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.ellipses × SpecTec.resulttype,
          SpecTec.Call.«$pop» c
            (.NoEllipses, [t]) irt⟩)
        middle (.success (.of (ellipses, ([] : List SpecTec.valtype))))
          fin := by
  rw [const_ok_success_iff]
  constructor
  · rintro ⟨hsyntax, hblock⟩
    exact ⟨hsyntax, (BlockTrace.block_success_iff c [] [t] [] xs n fin).1 hblock⟩
  · rintro ⟨hsyntax, htrace⟩
    exact ⟨hsyntax, (BlockTrace.block_success_iff c [] [t] [] xs n fin).2 htrace⟩

end properties.wasm_module_ok.ConstExactSyntaxBoundary
