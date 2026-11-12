import properties.wasm_module_ok.FreeListValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.FreeElemValidation

open properties.wasm_module_ok.FreeUnionValidation
open properties.wasm_module_ok.FreeListValidation

theorem free_elem_init_ref_func
    (e : SpecTec.elem) (init : SpecTec.const)
    (x : SpecTec.funcidx) (result : SpecTec.free)
    (n finalSupply : Nat)
    (hinit : init ∈ e.EINIT)
    (href : SpecTec.instr.«REF.FUNC» x ∈ init)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_elem» e⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.«$free_elem_clauses» e))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«$free_elem:clause:0» at hclause
      cases hclause with
      | bind_success hlist htail =>
        rename_i middle₁ initFree
        cases htail with
        | bind_success hmode htail =>
          rename_i middle₂ modeFree
          cases htail with
          | bind_success hunion hpure =>
            cases hpure with
            | pure =>
              have hpart : HasFunc initFree x :=
                free_list_preserves_funcs SpecTec.Call.«$free_const»
                  (fun a : SpecTec.const =>
                    SpecTec.instr.«REF.FUNC» x ∈ a) x
                  (by intro item out start finish hm hc
                      exact FreeConstValidation.free_const_ref_func
                        item x out start finish hm hc)
                  e.EINIT init hinit href initFree n middle₁ hlist
              exact free_union_preserves_funcs initFree modeFree result x
                middle₂ finalSupply hunion (.inl hpart)
    | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem free_elems_init_ref_func
    (es : List SpecTec.elem) (e : SpecTec.elem)
    (init : SpecTec.const) (x : SpecTec.funcidx)
    (result : SpecTec.free) (n finalSupply : Nat)
    (he : e ∈ es) (hinit : init ∈ e.EINIT)
    (href : SpecTec.instr.«REF.FUNC» x ∈ init)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$free_list» SpecTec.elem
          SpecTec.Call.«$free_elem» es⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  exact free_list_preserves_funcs SpecTec.Call.«$free_elem»
    (fun a : SpecTec.elem =>
      ∃ init : SpecTec.const, init ∈ a.EINIT ∧
        SpecTec.instr.«REF.FUNC» x ∈ init) x
    (by intro item out start finish hm hc
        obtain ⟨init, hi, hr⟩ := hm
        exact free_elem_init_ref_func item init x out start finish hi hr hc)
    es e he ⟨init, hinit, href⟩ result n finalSupply hcall

end properties.wasm_module_ok.FreeElemValidation
