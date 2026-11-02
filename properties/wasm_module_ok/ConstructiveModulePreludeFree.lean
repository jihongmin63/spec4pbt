import properties.wasm_module_ok.ConstructiveModulePrelude
import properties.wasm_module_ok.ConstructiveFreeCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModulePrelude
open SpecTec properties.wasm_module_ok SpecTecExecution

theorem constant_flat (c : context) (t : valtype) (xs : SpecTec.const) (n finish : Nat)
    (h : Eval specTecProgram (.call ⟨Unit,SpecTecCall.Const_ok c t xs⟩) n (.success (.of ())) finish) :
    ∀i∈xs,ConstructiveFreeConstants.Flat i := by
  have hs := (ConstExactSyntaxBoundary.const_ok_success_iff c t xs n finish).1 h |>.1
  exact fun i hi => ConstructiveFreeConstants.syntax_flat c i (hs i hi)

/-- Flat initializer syntax follows from each actually generated stage. No
validity trace for the new full module is assumed. -/
theorem prelude_flat (p : Result) : ConstructiveFreeModule.PreludeFlat (raw p) := by
  intro xs site
  cases site with
  | table t ht =>
    obtain ⟨c,vt,n,finish,hc⟩ := DeclarationConstValidation.tables_ok_member_const _ _ p.tables.items t 0 0
      (ConstructiveModuleTables.execute _ (boundedEnv p.before) p.tables 0) ht
    exact constant_flat c vt t.TINIT n finish hc
  | global g hg =>
    obtain ⟨c,vt,n,finish,hc⟩ := DeclarationConstValidation.globals_ok_member_const _ _ p.globals.items g 0 0
      (ConstructiveModuleGlobals.execute _ p.memories.env p.globals 0) hg
    exact constant_flat c vt g.GINIT n finish hc
  | elemInit e xs he hx =>
    obtain ⟨c,d,n,finish,hc⟩ := ElemDataCallValidation.elems_ok_member_call _ _ p.elements.items e 0 0 (p.elements.correct 0) he
    obtain ⟨⟨a,b,hi⟩,_⟩ := ElemDataConstValidation.elem_ok_initializer_and_mode c d e n finish hc
    obtain ⟨u,v,hx⟩ := ElemDataConstValidation.elem_iter_member_const c e.ETYPE e.EINIT a b hi xs hx
    exact constant_flat c (.RefT e.ETYPE) xs u v hx
  | elemOffset e a he ha =>
    obtain ⟨c,d,n,finish,hc⟩ := ElemDataCallValidation.elems_ok_member_call _ _ p.elements.items e 0 0 (p.elements.correct 0) he
    obtain ⟨_,⟨u,v,hm⟩⟩ := ElemDataConstValidation.elem_ok_initializer_and_mode c d e n finish hc
    rw [ha] at hm
    obtain ⟨vt,j,k,hx⟩ := ModeConstValidation.elemmode_active_const c e.ETYPE a u v hm
    exact constant_flat c vt a.OFFSET j k hx
  | dataOffset d a hd ha =>
    obtain ⟨c,e,n,finish,hc⟩ := ElemDataCallValidation.datas_ok_member_call _ _ p.data.items d 0 0 (p.data.correct 0) hd
    obtain ⟨u,v,hm⟩ := ElemDataConstValidation.data_ok_mode c e d n finish hc
    rw [ha] at hm
    obtain ⟨vt,j,k,hx⟩ := ModeConstValidation.datamode_active_const c a u v hm
    exact constant_flat c vt a.OFFSET j k hx

theorem initializer_available (p : Result) (xs : List instr) (hsite : ConstructiveRefs.InitializerSite (raw p) xs)
    (x : Nat) (hx : instr.«REF.FUNC» x∈xs) :
    FreeUnionValidation.HasFunc (ConstructiveFreeModule.moduleFree (raw p)) x :=
  RefCyclePrestage.direct_hasFunc_free (raw p) _ 0
    (ConstructiveFreeModule.module_free_total (raw p) 0 (prelude_flat p)) x
    (ConstructiveRefs.initializer_direct (raw p) xs hsite x hx)
#print axioms prelude_flat
#print axioms initializer_available
end properties.wasm_module_ok.ConstructiveModulePrelude
