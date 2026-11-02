import properties.wasm_module_ok.FreeConstValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.FreeDeclarationValidation

open properties.wasm_module_ok.FreeUnionValidation
open properties.wasm_module_ok.FreeConstValidation

theorem free_global_ref_func
    (g : SpecTec.global) (x : SpecTec.funcidx)
    (result : SpecTec.free) (n finalSupply : Nat)
    (hmem : SpecTec.instr.«REF.FUNC» x ∈ g.GINIT)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.free, SpecTec.SpecTecCall.«$free_global» g⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$free_global_clauses» g) ())
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«$free_global:clause:0» at hclause
      cases hclause with
      | bind_success htype htail =>
        rename_i middle₁ typeFree
        cases htail with
        | bind_success hconst htail =>
          rename_i middle₂ constFree
          cases htail with
          | bind_success hunion hpure =>
            cases hpure with
            | pure =>
              exact free_union_preserves_funcs typeFree constFree result x
                middle₂ finalSupply hunion
                (.inr (free_const_ref_func g.GINIT x constFree middle₁ middle₂
                  hmem hconst))
    | orElse_unmatch _ hnone => cases hnone

theorem free_table_ref_func
    (t : SpecTec.table) (x : SpecTec.funcidx)
    (result : SpecTec.free) (n finalSupply : Nat)
    (hmem : SpecTec.instr.«REF.FUNC» x ∈ t.TINIT)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.free, SpecTec.SpecTecCall.«$free_table» t⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$free_table_clauses» t) ())
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«$free_table:clause:0» at hclause
      cases hclause with
      | bind_success htype htail =>
        rename_i middle₁ typeFree
        cases htail with
        | bind_success hconst htail =>
          rename_i middle₂ constFree
          cases htail with
          | bind_success hunion hpure =>
            cases hpure with
            | pure =>
              exact free_union_preserves_funcs typeFree constFree result x
                middle₂ finalSupply hunion
                (.inr (free_const_ref_func t.TINIT x constFree middle₁ middle₂
                  hmem hconst))
    | orElse_unmatch _ hnone => cases hnone

end properties.wasm_module_ok.FreeDeclarationValidation
