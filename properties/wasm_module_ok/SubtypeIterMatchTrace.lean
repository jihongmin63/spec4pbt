import properties.wasm_module_ok.SubtypeStaticMatchTrace
import properties.wasm_module_ok.SubtypeListShape
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.SubtypeIterMatchTrace

theorem subtype_sub_iter_static_call
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (strt : SpecTec.strtype) (hts : List SpecTec.heaptype)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.«Subtype_sub_ok:rule:iter:0» c x strt hts⟩)
      start (.success (.of ())) finish) :
    ∀ ht ∈ hts, ∃ y : SpecTec.typeidx,
      ht = .VarHT (.StatX y) ∧
      ∃ callStart callFinish : Nat,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Unit, SpecTec.Call.Subtype_sub_ok' c x strt
            (.VarHT (.StatX y))⟩)
          callStart (.success (.of ())) callFinish := by
  induction hts generalizing start finish with
  | nil =>
      intro ht hmem
      cases hmem
  | cons hd tl ih =>
      cases h with
      | call hbody =>
          change SpecTecExecution.Eval SpecTec.Body
            (SpecTecExecution.tryClauses
              (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses»
                c x strt (hd :: tl)))
            start (.success (.of ())) finish at hbody
          obtain ⟨idx, hselected⟩ :=
            (properties.wasm_module_ok.Execution.tryClauses_success_iff
              (SpecTec.«Subtype_sub_ok:rule:iter:0_clauses»
                c x strt (hd :: tl))
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
                            obtain ⟨y, hshape, _⟩ :=
                              SubtypeSupertypeShape.subtype_sub_ok_prime_shape
                                c x strt hd _ _ hhead
                            exact ⟨y, hshape, start, _,
                              by simpa [hshape] using hhead⟩
                          · exact ih _ _ htail ht htlmem
              | next _ hrest => cases hrest

theorem subtype_sub_ok_static_call
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (fin : SpecTec.final) (hts : List SpecTec.heaptype)
    (strt : SpecTec.strtype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Subtype_sub_ok c x
        (.SubT fin hts strt)⟩)
      start (.success (.of ())) finish) :
    ∀ ht ∈ hts, ∃ y : SpecTec.typeidx,
      ht = .VarHT (.StatX y) ∧
      ∃ callStart callFinish : Nat,
        SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Unit, SpecTec.Call.Subtype_sub_ok' c x strt
            (.VarHT (.StatX y))⟩)
          callStart (.success (.of ())) callFinish := by
  cases h with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Subtype_sub_ok_clauses c x (.SubT fin hts strt)))
        start (.success (.of ())) finish at hbody
      obtain ⟨idx, hselected⟩ :=
        (properties.wasm_module_ok.Execution.tryClauses_success_iff
          (SpecTec.Subtype_sub_ok_clauses c x (.SubT fin hts strt))
          start (.of ()) finish).1 hbody
      unfold SpecTec.Subtype_sub_ok_clauses at hselected
      cases hselected with
      | here h0 =>
          unfold SpecTec.«Subtype_sub_ok:clause:0» at h0
          dsimp only at h0
          cases h0 with
          | bind_success hiter _ =>
              exact subtype_sub_iter_static_call c x strt hts _ _ hiter
      | next _ hrest => cases hrest

end properties.wasm_module_ok.SubtypeIterMatchTrace
