import properties.wasm_module_ok.ConstructiveModuleModeRefs
import properties.wasm_module_ok.ConstructiveModuleElemDataRules
import properties.wasm_module_ok.ModeConstValidation
import properties.wasm_module_ok.CandidateProvenanceElemDataFuncs
import properties.wasm_module_ok.ElemInitDecision
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleElemDataRefs
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructivePreludeRefs ConstructiveModuleModeRefs

abbrev ElementAvailable (refs : SpecTec.free) (e : SpecTec.elem) :=
  (∀xs∈e.EINIT,Available refs xs) ∧ ElemAvailable refs e.EMODE
abbrev DataAvailable (refs : SpecTec.free) (d : SpecTec.data) := ConstructiveModuleModeRefs.DataAvailable refs d.DMODE

theorem initializers_replace (refs : SpecTec.free) (c : context) (rt : reftype) (codes : List (List instr)) (n finish : Nat)
    (ha : ∀xs∈codes,Available refs xs)
    (h : Eval specTecProgram (.call ⟨Unit,SpecTecCall.«Elem_ok:rule:iter:0» c rt codes⟩) n (.success (.of ())) finish) :
    Eval specTecProgram (.call ⟨Unit,SpecTecCall.«Elem_ok:rule:iter:0» (replace refs c) rt codes⟩) n (.success (.of ())) finish := by
  induction codes generalizing n with
  | nil =>
    exact (ElemInitDecision.elem_iter_nil_success_iff _ rt n finish).2
      ((ElemInitDecision.elem_iter_nil_success_iff c rt n finish).1 h)
  | cons xs codes ih =>
    obtain ⟨middle,hh,ht⟩ := (ElemDataConstValidation.elem_iter_cons_success_iff c rt xs codes n finish).1 h
    exact (ElemDataConstValidation.elem_iter_cons_success_iff _ rt xs codes n finish).2
      ⟨middle,ConstructiveRefs.const_ok_replace_refs c refs _ xs n middle (ha xs (by simp)) hh,
        ih middle (fun ys hy => ha ys (by simp [hy])) ht⟩

theorem elem_replace (refs : SpecTec.free) (c out : context) (e : SpecTec.elem) (n finish : Nat)
    (ha : ElementAvailable refs e)
    (h : Eval specTecProgram (.call ⟨context,SpecTecCall.Elem_ok c e⟩) n (.success (.of out)) finish) :
    Eval specTecProgram (.call ⟨context,SpecTecCall.Elem_ok (replace refs c) e⟩) n (.success (.of (replace refs out))) finish := by
  obtain ⟨n1,n2,hr,hi,hm,ho⟩ := ConstructiveModuleElemDataRules.elem_original c out e n finish h
  have hv := (ReftypeTotal.reftype_success_iff_valid c e.ETYPE n n1).1 hr
  have hr' := (ReftypeTotal.reftype_success_iff_valid (replace refs c) e.ETYPE n n1).2 hv
  rw [ho]
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.Elem_ok_clauses (replace refs c) e) ()) n _ finish
  apply firstSuccess_cons_success
  unfold SpecTec.«Elem_ok:clause:0»
  apply Eval.bind_success hr'
  apply Eval.bind_success (initializers_replace refs c e.ETYPE e.EINIT n1 n2 ha.1 hi)
  apply Eval.bind_success (ConstructiveModuleModeRefs.elem_replace refs c e.ETYPE e.EMODE n2 finish ha.2 hm)
  exact Eval.pure _

theorem data_replace (refs : SpecTec.free) (c out : context) (e : SpecTec.data) (n finish : Nat)
    (ha : DataAvailable refs e)
    (h : Eval specTecProgram (.call ⟨context,SpecTecCall.Data_ok c e⟩) n (.success (.of out)) finish) :
    Eval specTecProgram (.call ⟨context,SpecTecCall.Data_ok (replace refs c) e⟩) n (.success (.of (replace refs out))) finish := by
  obtain ⟨hm,ho⟩ := ConstructiveModuleElemDataRules.data_original c out e n finish h
  rw [ho]
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.Data_ok_clauses (replace refs c) e) ()) n _ finish
  apply firstSuccess_cons_success
  unfold SpecTec.«Data_ok:clause:0»
  exact Eval.bind_success (ConstructiveModuleModeRefs.data_replace refs c e.DMODE n finish ha hm) (Eval.pure _)

theorem elem_bounded (c out : context) (e : SpecTec.elem) (n finish : Nat)
    (h : Eval specTecProgram (.call ⟨context,SpecTecCall.Elem_ok c e⟩) n (.success (.of out)) finish) :
    ElementAvailable (ConstructiveModuleRefsBounds.allFunctions c) e := by
  obtain ⟨n1,n2,hr,hi,hm,ho⟩ := ConstructiveModuleElemDataRules.elem_original c out e n finish h
  constructor
  · intro xs hxs x hx
    obtain ⟨a,b,hc⟩ := ElemDataConstValidation.elem_iter_member_const c e.ETYPE e.EINIT n1 n2 hi xs hxs
    exact ConstructiveModuleRefsBounds.allFunctions_has c x (ConstructiveModuleRefsBounds.constant_bound c _ xs a b hc x hx)
  · cases he : e.EMODE with
    | Passive => trivial
    | Declarative => trivial
    | Active a =>
      rw [he] at hm
      obtain ⟨vt,j,k,hc⟩ := ModeConstValidation.elemmode_active_const c e.ETYPE a n2 finish hm
      intro x hx
      exact ConstructiveModuleRefsBounds.allFunctions_has c x (ConstructiveModuleRefsBounds.constant_bound c vt a.OFFSET j k hc x hx)

theorem data_bounded (c out : context) (e : SpecTec.data) (n finish : Nat)
    (h : Eval specTecProgram (.call ⟨context,SpecTecCall.Data_ok c e⟩) n (.success (.of out)) finish) :
    DataAvailable (ConstructiveModuleRefsBounds.allFunctions c) e := by
  obtain ⟨hm,_⟩ := ConstructiveModuleElemDataRules.data_original c out e n finish h
  change ConstructiveModuleModeRefs.DataAvailable (ConstructiveModuleRefsBounds.allFunctions c) e.DMODE
  cases he : e.DMODE with
  | Passive => trivial
  | Active a =>
    rw [he] at hm
    obtain ⟨addr,lim,hx,hc⟩ := ConstructiveModuleModeRules.data_active_original c a n finish hm
    intro x hmem
    exact ConstructiveModuleRefsBounds.allFunctions_has c x (ConstructiveModuleRefsBounds.constant_bound c _ a.OFFSET n finish hc x hmem)

#print axioms elem_replace
#print axioms data_replace
#print axioms elem_bounded
#print axioms data_bounded
end properties.wasm_module_ok.ConstructiveModuleElemDataRefs
