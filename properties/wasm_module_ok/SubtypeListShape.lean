import properties.wasm_module_ok.SubtypeSupertypeShape
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.SubtypeListShape

theorem subtype_sub_iter_all_static
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (strt : SpecTec.strtype) (hts : List SpecTec.heaptype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Subtype_sub_ok:rule:iter:0» c x strt hts⟩)
      start (.success (.of ())) finish) :
    ∀ ht ∈ hts,
      ∃ y : SpecTec.typeidx,
        ht = .VarHT (.StatX y) ∧ y < x := by
  induction hts generalizing start finish with
  | nil =>
      intro ht hmem
      cases hmem
  | cons hd tl ih =>
      cases h with
      | call hbody =>
        change SpecTecExecution.Eval SpecTec.Body
          (SpecTecExecution.tryClauses
            (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» c x strt (hd :: tl)))
          start (.success (.of ())) finish at hbody
        obtain ⟨idx, hselected⟩ :=
          (properties.wasm_module_ok.Execution.tryClauses_success_iff
            (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» c x strt (hd :: tl))
            start (.of ()) finish).1 hbody
        unfold SpecTec.«Subtype_sub_ok:rule:iter:0_clauses» at hselected
        cases hselected with
        | here h0 =>
          unfold SpecTec.«Subtype_sub_ok:rule:iter:0:clause:0» at h0
          cases h0
        | next _ hrest =>
          cases hrest with
          | here h1 =>
            unfold SpecTec.«Subtype_sub_ok:rule:iter:0:clause:1» at h1
            cases h1 with
            | bind_success hhead htailplan =>
              cases htailplan with
              | bind_success htail _ =>
                intro ht hmem
                rcases List.mem_cons.mp hmem with heq | htlmem
                · subst ht
                  exact properties.wasm_module_ok.SubtypeSupertypeShape.subtype_sub_ok_prime_shape
                    c x strt hd _ _ hhead
                · exact ih _ _ htail ht htlmem
          | next _ hrest => cases hrest

end properties.wasm_module_ok.SubtypeListShape
