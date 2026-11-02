import properties.wasm_module_ok.FreeConstValidation
import properties.wasm_module_ok.FreeElemValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.FreeOffsetValidation

open properties.wasm_module_ok.FreeUnionValidation
open properties.wasm_module_ok.FreeConstValidation

theorem free_elemmode_active_ref_func
    (a : SpecTec.active) (x : SpecTec.funcidx)
    (result : SpecTec.free) (n finalSupply : Nat)
    (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$free_elemmode»
          SpecTec.Call.«$update_tables» (.Active a)⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (.orElse
        (SpecTec.«$free_elemmode:clause:0»
          SpecTec.Call.«$update_tables» (.Active a))
        (fun _ => SpecTecExecution.tryClauses
          [SpecTec.«$free_elemmode:clause:1»
            SpecTec.Call.«$update_tables» (.Active a)]))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«$free_elemmode:clause:0» at hfirst
      cases hfirst with
      | bind_success hguard _ =>
        cases hguard with
        | guard_true hfalse => simp at hfalse
    | orElse_unmatch hfailedSupply htail =>
      restore_supply hfailedSupply at htail
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse
          (SpecTec.«$free_elemmode:clause:1»
            SpecTec.Call.«$update_tables» (.Active a))
          (fun _ => .unmatch))
        n (.success (.of result)) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«$free_elemmode:clause:1» at hsecond
        cases hsecond with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true _ =>
            cases htail with
            | bind_success hupdate htail =>
              rename_i middle₁ updateFree
              cases htail with
              | bind_success hconst htail =>
                rename_i middle₂ constFree
                cases htail with
                | bind_success hunion hpure =>
                  cases hpure with
                  | pure =>
                    exact free_union_preserves_funcs updateFree constFree
                      result x middle₂ finalSupply hunion
                      (.inr (free_const_ref_func a.OFFSET x constFree
                        middle₁ middle₂ href hconst))
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem free_datamode_active_ref_func
    (a : SpecTec.active) (x : SpecTec.funcidx)
    (result : SpecTec.free) (n finalSupply : Nat)
    (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$free_datamode»
          SpecTec.Call.«$update_mems» (.Active a)⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (.orElse
        (SpecTec.«$free_datamode:clause:0»
          SpecTec.Call.«$update_mems» (.Active a))
        (fun _ => SpecTecExecution.tryClauses
          [SpecTec.«$free_datamode:clause:1»
            SpecTec.Call.«$update_mems» (.Active a)]))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hfirst =>
      unfold SpecTec.«$free_datamode:clause:0» at hfirst
      cases hfirst with
      | bind_success hguard _ =>
        cases hguard with
        | guard_true hfalse => simp at hfalse
    | orElse_unmatch hfailedSupply htail =>
      restore_supply hfailedSupply at htail
      change SpecTecExecution.Eval SpecTec.Body
        (.orElse
          (SpecTec.«$free_datamode:clause:1»
            SpecTec.Call.«$update_mems» (.Active a))
          (fun _ => .unmatch))
        n (.success (.of result)) finalSupply at htail
      cases htail with
      | orElse_success hsecond =>
        unfold SpecTec.«$free_datamode:clause:1» at hsecond
        cases hsecond with
        | bind_success hguard htail =>
          cases hguard with
          | guard_true _ =>
            cases htail with
            | bind_success hupdate htail =>
              rename_i middle₁ updateFree
              cases htail with
              | bind_success hconst htail =>
                rename_i middle₂ constFree
                cases htail with
                | bind_success hunion hpure =>
                  cases hpure with
                  | pure =>
                    exact free_union_preserves_funcs updateFree constFree
                      result x middle₂ finalSupply hunion
                      (.inr (free_const_ref_func a.OFFSET x constFree
                        middle₁ middle₂ href hconst))
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem free_elem_active_offset_ref_func
    (e : SpecTec.elem) (a : SpecTec.active)
    (x : SpecTec.funcidx) (result : SpecTec.free)
    (n finalSupply : Nat)
    (hmode : e.EMODE = .Active a)
    (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET)
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
        | bind_success hmodecall htail =>
          rename_i middle₂ modeFree
          cases htail with
          | bind_success hunion hpure =>
            cases hpure with
            | pure =>
              have hmodefree : HasFunc modeFree x :=
                free_elemmode_active_ref_func a x modeFree middle₁ middle₂
                  href (hmode ▸ hmodecall)
              exact free_union_preserves_funcs initFree modeFree result x
                middle₂ finalSupply hunion (.inr hmodefree)
    | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem free_data_active_offset_ref_func
    (d : SpecTec.data) (a : SpecTec.active)
    (x : SpecTec.funcidx) (result : SpecTec.free)
    (n finalSupply : Nat)
    (hmode : d.DMODE = .Active a)
    (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_data» d⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  cases hcall with
  | call hbody =>
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.«$free_data_clauses» d))
      n (.success (.of result)) finalSupply at hbody
    cases hbody with
    | orElse_success hclause =>
      unfold SpecTec.«$free_data:clause:0» at hclause
      cases hclause with
      | bind_success hmodecall hpure =>
        cases hpure with
        | pure =>
          exact free_datamode_active_ref_func a x result n finalSupply
            href (hmode ▸ hmodecall)
    | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem free_elems_active_offset_ref_func
    (es : List SpecTec.elem) (e : SpecTec.elem)
    (a : SpecTec.active) (x : SpecTec.funcidx)
    (result : SpecTec.free) (n finalSupply : Nat)
    (he : e ∈ es) (hmode : e.EMODE = .Active a)
    (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$free_list» SpecTec.elem
          SpecTec.Call.«$free_elem» es⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  exact FreeListValidation.free_list_preserves_funcs
    SpecTec.Call.«$free_elem»
    (fun e : SpecTec.elem =>
      ∃ a : SpecTec.active, e.EMODE = .Active a ∧
        SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET) x
    (by intro item out start finish hm hc
        obtain ⟨a, hmode, href⟩ := hm
        exact free_elem_active_offset_ref_func item a x out start finish
          hmode href hc)
    es e he ⟨a, hmode, href⟩ result n finalSupply hcall

theorem free_datas_active_offset_ref_func
    (ds : List SpecTec.data) (d : SpecTec.data)
    (a : SpecTec.active) (x : SpecTec.funcidx)
    (result : SpecTec.free) (n finalSupply : Nat)
    (hd : d ∈ ds) (hmode : d.DMODE = .Active a)
    (href : SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET)
    (hcall : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free,
        SpecTec.Call.«$free_list» SpecTec.data
          SpecTec.Call.«$free_data» ds⟩)
      n (.success (.of result)) finalSupply) : HasFunc result x := by
  exact FreeListValidation.free_list_preserves_funcs
    SpecTec.Call.«$free_data»
    (fun d : SpecTec.data =>
      ∃ a : SpecTec.active, d.DMODE = .Active a ∧
        SpecTec.instr.«REF.FUNC» x ∈ a.OFFSET) x
    (by intro item out start finish hm hc
        obtain ⟨a, hmode, href⟩ := hm
        exact free_data_active_offset_ref_func item a x out start finish
          hmode href hc)
    ds d hd ⟨a, hmode, href⟩ result n finalSupply hcall


end properties.wasm_module_ok.FreeOffsetValidation
