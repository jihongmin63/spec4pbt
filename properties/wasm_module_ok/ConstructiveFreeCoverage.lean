import properties.wasm_module_ok.ConstructiveFreeModule
import properties.wasm_module_ok.DeclarationConstValidation
import properties.wasm_module_ok.ModeConstValidation
import properties.wasm_module_ok.Validity
import properties.wasm_module_ok.Execution
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveFreeCoverage
open SpecTec SpecTecExecution
open properties.wasm_module_ok
open properties.wasm_module_ok.ConstructiveFreeConstants properties.wasm_module_ok.ConstructiveFreeModule

private theorem constant_flat (c : context) (t : valtype) (xs : SpecTec.const)
    (n finish : Nat)
    (h : Eval Body (.call ⟨Unit, Call.Const_ok c t xs⟩)
      n (.success (.of ())) finish) : ∀ i ∈ xs, Flat i := by
  have hs := (ConstExactSyntaxBoundary.const_ok_success_iff c t xs n finish).1 h |>.1
  exact fun i hi => syntax_flat c i (hs i hi)

/-- Backward coverage only: every original valid module belongs to the structural
summary domain. Forward summary soundness never assumes a ModuleOkTrace. -/
theorem module_ok_prelude_flat (m : SpecTec.module) (h : SpecTec.Module_ok m) :
    PreludeFlat m := by
  obtain ⟨tr⟩ := Validity.module_ok_full_trace m h
  intro xs hsite
  cases hsite with
  | table t ht =>
    obtain ⟨c, vt, n, fin, hc⟩ := DeclarationConstValidation.tables_ok_member_const
      tr.c2 tr.c3 m.TABLES t tr.n5 tr.n6 tr.tables_ok ht
    exact constant_flat c vt t.TINIT n fin hc
  | global g hg =>
    obtain ⟨c, vt, n, fin, hc⟩ := DeclarationConstValidation.globals_ok_member_const
      tr.c4 tr.c5 m.GLOBALS g tr.n7 tr.n8 tr.globals_ok hg
    exact constant_flat c vt g.GINIT n fin hc
  | elemInit e xs he hx =>
    obtain ⟨c, d, n, fin, hc⟩ := ElemDataCallValidation.elems_ok_member_call
      tr.c6 tr.c7 m.ELEMS e tr.n9 tr.n10 tr.elems_ok he
    obtain ⟨⟨a, b, hi⟩, _⟩ := ElemDataConstValidation.elem_ok_initializer_and_mode c d e n fin hc
    obtain ⟨u, v, hx⟩ := ElemDataConstValidation.elem_iter_member_const c e.ETYPE e.EINIT a b hi xs hx
    exact constant_flat c (.RefT e.ETYPE) xs u v hx
  | elemOffset e a he ha =>
    obtain ⟨c, d, n, fin, hc⟩ := ElemDataCallValidation.elems_ok_member_call
      tr.c6 tr.c7 m.ELEMS e tr.n9 tr.n10 tr.elems_ok he
    obtain ⟨_, ⟨u, v, hm⟩⟩ := ElemDataConstValidation.elem_ok_initializer_and_mode c d e n fin hc
    rw [ha] at hm
    obtain ⟨vt, j, k, hx⟩ := ModeConstValidation.elemmode_active_const c e.ETYPE a u v hm
    exact constant_flat c vt a.OFFSET j k hx
  | dataOffset d a hd ha =>
    obtain ⟨c, e, n, fin, hc⟩ := ElemDataCallValidation.datas_ok_member_call
      tr.c7 tr.c8 m.DATAS d tr.n10 tr.n11 tr.datas_ok hd
    obtain ⟨u, v, hm⟩ := ElemDataConstValidation.data_ok_mode c e d n fin hc
    rw [ha] at hm
    obtain ⟨vt, j, k, hx⟩ := ModeConstValidation.datamode_active_const c a u v hm
    exact constant_flat c vt a.OFFSET j k hx

theorem module_free_exact (m : SpecTec.module) (h : PreludeFlat m)
    (result : free) (n finish : Nat) :
    Eval Body (.call ⟨free, Call.«$free_module»
      ({{m with FUNCS := []} with START := none})⟩)
      n (.success (.of result)) finish ↔ result = moduleFree m ∧ finish = n := by
  constructor
  · intro he
    obtain ⟨hv, hn⟩ := properties.wasm_module_ok.Execution.eval_deterministic he (module_free_total m n h)
    cases hv
    exact ⟨rfl, hn⟩
  · rintro ⟨rfl, rfl⟩
    exact module_free_total m finish h

/-- Total executable reference summary for every original valid module. -/
theorem module_ok_computed_refs (m : SpecTec.module) (h : SpecTec.Module_ok m) (n : Nat) :
    Eval Body (.call ⟨free, Call.«$free_module»
      ({{m with FUNCS := []} with START := none})⟩)
      n (.success (.of (moduleFree m))) n :=
  module_free_total m n (module_ok_prelude_flat m h)

end properties.wasm_module_ok.ConstructiveFreeCoverage
