import properties.wasm_module_ok.StackValidation
import properties.wasm_module_ok.InstrsValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.BlockTrace

theorem block_success_iff
    (c : SpecTec.context)
    (inputs outputs : List SpecTec.valtype)
    (localIndices : List SpecTec.localidx)
    (body : SpecTec.const) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Block_ok c
        (.InstrT inputs outputs localIndices) body⟩)
      n (.success (.of ())) finalSupply ↔
    ∃ (irt : SpecTec.inferresulttype) (indices : List SpecTec.idx)
      (ellipses : SpecTec.ellipses) (middle : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
          SpecTec.Call.Instrs_ok c
            (.NoEllipses, inputs) body⟩)
        n (.success (.of (irt, indices))) middle ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.ellipses × SpecTec.resulttype,
          SpecTec.Call.«$pop» c
            (.NoEllipses, outputs) irt⟩)
        middle (.success (.of (ellipses, ([] : List SpecTec.valtype))))
          finalSupply := by
  constructor
  · intro h
    cases h with
    | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse (SpecTec.«Block_ok:clause:0» c
            (.InstrT inputs outputs localIndices) body)
          (fun _ => .unmatch))
        n (.success (.of ())) finalSupply at hbody
      cases hbody with
      | orElse_success hclause =>
        unfold SpecTec.«Block_ok:clause:0» at hclause
        cases hclause with
        | bind_success hstack htail =>
          rename_i stackSupply stackResult
          obtain ⟨hstackResult, hstackSupply⟩ :=
            (StackValidation.stack_success_iff inputs
              stackResult n stackSupply).1 hstack
          subst stackResult
          subst stackSupply
          cases htail with
          | bind_success hinstr htail =>
            rename_i middle instrResult
            cases instrResult with
            | mk irt indices =>
              cases htail with
              | bind_success hstack2 htail =>
                rename_i stackSupply2 stackResult2
                obtain ⟨hstackResult2, hstackSupply2⟩ :=
                  (StackValidation.stack_success_iff outputs
                    stackResult2 middle stackSupply2).1 hstack2
                subst stackResult2
                subst stackSupply2
                cases htail with
                | bind_success hpop htail =>
                  rename_i popSupply popResult
                  cases popResult with
                  | mk ellipses remain =>
                    cases htail with
                    | bind_success hguard hpure =>
                      cases hguard with
                      | guard_true hempty =>
                        cases hpure with
                        | pure =>
                          cases hempty
                          exact ⟨irt, indices, ellipses, middle,
                            hinstr, hpop⟩
      | orElse_unmatch _ hlast => cases hlast
  · rintro ⟨irt, indices, ellipses, middle, hinstr, hpop⟩
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Block_ok_clauses c
          (.InstrT inputs outputs localIndices) body))
      n (.success (.of ())) finalSupply
    apply SpecTecExecution.tryClauses_cons_success
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Block_ok:clause:0» c
        (.InstrT inputs outputs localIndices) body)
      n (.success (.of ())) finalSupply
    unfold SpecTec.«Block_ok:clause:0»
    apply SpecTecExecution.Eval.bind_success
      (StackValidation.stack_total inputs n)
    apply SpecTecExecution.Eval.bind_success hinstr
    apply SpecTecExecution.Eval.bind_success
      (StackValidation.stack_total outputs middle)
    apply SpecTecExecution.Eval.bind_success hpop
    apply SpecTecExecution.Eval.bind_success
    · apply SpecTecExecution.Eval.guard_true
      rfl
    · exact SpecTecExecution.Eval.pure ()

end properties.wasm_module_ok.BlockTrace
