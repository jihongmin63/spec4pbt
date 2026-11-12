import properties.wasm_module_ok.FreeUnionValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.FreeConstValidation

open properties.wasm_module_ok.FreeUnionValidation

theorem free_block_ref_func
    (xs : List SpecTec.instr) (x : SpecTec.funcidx)
    (result : SpecTec.free) (n finalSupply : Nat)
    (hmem : SpecTec.instr.«REF.FUNC» x ∈ xs)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_block» xs⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.«$free_block_clauses» xs))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«$free_block:clause:0» at hclause
      cases hclause with
      | bind_success hlist htail =>
        rename_i middle₁ listFree
        cases htail with
        | bind_success hshift hpure =>
          cases hpure with
          | pure =>
            simpa [HasFunc] using
              (free_instr_list_ref_func xs x listFree n middle₁ hmem hlist)
    | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem free_const_ref_func
    (xs : List SpecTec.instr) (x : SpecTec.funcidx)
    (result : SpecTec.free) (n finalSupply : Nat)
    (hmem : SpecTec.instr.«REF.FUNC» x ∈ xs)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_const» xs⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.«$free_const_clauses» xs))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«$free_const:clause:0» at hclause
      cases hclause with
      | bind_success hblock hpure =>
        cases hpure with
        | pure => exact free_block_ref_func xs x result n finalSupply hmem hblock
    | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

end properties.wasm_module_ok.FreeConstValidation
