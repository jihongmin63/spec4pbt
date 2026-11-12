import properties.wasm_module_ok.ActualSupertypeCases
import properties.wasm_module_ok.MatchHeaptypeBasic
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.SubtypeSupertypeShape

theorem subtype_sub_ok_prime_shape
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (strt : SpecTec.strtype) (ht : SpecTec.heaptype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Subtype_sub_ok' c x strt ht⟩)
      start (.success (.of ())) finish) :
    ∃ y : SpecTec.typeidx, ht = .VarHT (.StatX y) ∧ y < x := by
  cases h with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Subtype_sub_ok'_clauses c x strt ht))
        start (.success (.of ())) finish at hbody
      obtain ⟨idx, hselected⟩ :=
        (properties.wasm_module_ok.Execution.tryClauses_success_iff
          (SpecTec.Subtype_sub_ok'_clauses c x strt ht)
          start (.of ()) finish).1 hbody
      unfold SpecTec.Subtype_sub_ok'_clauses at hselected
      cases hselected with
      | here h0 =>
          cases ht <;> simp [SpecTec.«Subtype_sub_ok':clause:0»,
            SpecTec.«sub:heaptype:heaptypeVar»,
            SpecTec.«Subtype_sub_ok':rule:downcast:0»] at h0 <;> cases h0
          all_goals
            rename_i mid v hguard htail
            cases hguard
            try cases ‹False›
          cases ‹SpecTec.typevar› with
          | StatX y =>
              have hcall : SpecTecExecution.Eval SpecTec.Body
                  (.call ⟨Unit, SpecTec.Call.Subtype_sub_ok' c x strt
                    (.VarHT (.StatX y))⟩)
                  start (.success (.of ())) finish := .call hbody
              exact ⟨y, rfl,
                properties.wasm_module_ok.MatchHeaptypeBasic.subtype_sub_ok_static_lt
                  c x y strt start finish hcall⟩
          | RecX q =>
              simp [SpecTec.«exec:match:typevar:StatX»] at htail
              cases htail
              rename_i mid value hguard hrest
              cases hguard
              cases ‹False›
      | next _ hrest => cases hrest

end properties.wasm_module_ok.SubtypeSupertypeShape
