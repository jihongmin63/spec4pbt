import properties.wasm_module_ok.ConstructiveModuleElemDataRefs
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleElemDataRefs
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructivePreludeRefs

theorem elems_replace (refs : SpecTec.free) (c out : context) (xs : List SpecTec.elem) (n finish : Nat)
    (ha : ∀item∈xs,ElementAvailable refs item)
    (h : Eval Body (.call ⟨context,Call.Elems_ok c xs⟩) n (.success (.of out)) finish) :
    Eval Body (.call ⟨context,Call.Elems_ok (replace refs c) xs⟩)
      n (.success (.of (replace refs out))) finish := by
  induction xs generalizing c n with
  | nil =>
    obtain ⟨he,hn⟩ := ConstructiveModuleElemDataRules.elems_nil c out n finish h
    subst out;subst finish
    exact EmptyStageValidation.elems_nil_total _ n
  | cons item xs ih =>
    obtain ⟨next,middle,hh,ht⟩ := ConstructiveModuleElemDataRules.elems_original c out item xs n finish h
    exact ConstructiveModuleElemDataRules.elems_cons _ _ _ item xs n middle finish
      (elem_replace refs c next item n middle (ha item (by simp)) hh)
      (ih next middle (fun item hm => ha item (by simp [hm])) ht)

theorem elems_bounded (c out : context) (xs : List SpecTec.elem) (n finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Elems_ok c xs⟩) n (.success (.of out)) finish) :
    ∀item∈xs,ElementAvailable (ConstructiveModuleRefsBounds.allFunctions c) item := by
  induction xs generalizing c n with
  | nil => simp
  | cons item xs ih =>
    obtain ⟨next,middle,hh,ht⟩ := ConstructiveModuleElemDataRules.elems_original c out item xs n finish h
    intro e he
    rcases List.mem_cons.mp he with he|he
    · subst e;exact elem_bounded c next item n middle hh
    · have hb := ih next middle ht e he
      have hf := CandidateProvenanceElemDataFuncs.elem_ok_funcs c next item n middle hh
      have heq : ConstructiveModuleRefsBounds.allFunctions next=ConstructiveModuleRefsBounds.allFunctions c := by
        simp only [ConstructiveModuleRefsBounds.allFunctions,hf]
      exact heq ▸ hb

theorem datas_replace (refs : SpecTec.free) (c out : context) (xs : List SpecTec.data) (n finish : Nat)
    (ha : ∀item∈xs,DataAvailable refs item)
    (h : Eval Body (.call ⟨context,Call.Datas_ok c xs⟩) n (.success (.of out)) finish) :
    Eval Body (.call ⟨context,Call.Datas_ok (replace refs c) xs⟩)
      n (.success (.of (replace refs out))) finish := by
  induction xs generalizing c n with
  | nil =>
    obtain ⟨he,hn⟩ := ConstructiveModuleElemDataRules.datas_nil c out n finish h
    subst out;subst finish
    exact EmptyStageValidation.datas_nil_total _ n
  | cons item xs ih =>
    obtain ⟨next,middle,hh,ht⟩ := ConstructiveModuleElemDataRules.datas_original c out item xs n finish h
    exact ConstructiveModuleElemDataRules.datas_cons _ _ _ item xs n middle finish
      (data_replace refs c next item n middle (ha item (by simp)) hh)
      (ih next middle (fun item hm => ha item (by simp [hm])) ht)

theorem datas_bounded (c out : context) (xs : List SpecTec.data) (n finish : Nat)
    (h : Eval Body (.call ⟨context,Call.Datas_ok c xs⟩) n (.success (.of out)) finish) :
    ∀item∈xs,DataAvailable (ConstructiveModuleRefsBounds.allFunctions c) item := by
  induction xs generalizing c n with
  | nil => simp
  | cons item xs ih =>
    obtain ⟨next,middle,hh,ht⟩ := ConstructiveModuleElemDataRules.datas_original c out item xs n finish h
    intro e he
    rcases List.mem_cons.mp he with he|he
    · subst e;exact data_bounded c next item n middle hh
    · have hb := ih next middle ht e he
      have hf := CandidateProvenanceElemDataFuncs.data_ok_funcs c next item n middle hh
      have heq : ConstructiveModuleRefsBounds.allFunctions next=ConstructiveModuleRefsBounds.allFunctions c := by
        simp only [ConstructiveModuleRefsBounds.allFunctions,hf]
      exact heq ▸ hb

#print axioms elems_replace
#print axioms datas_replace
#print axioms elems_bounded
#print axioms datas_bounded
end properties.wasm_module_ok.ConstructiveModuleElemDataRefs
