import properties.wasm_module_ok.ConstructiveBodyAggregateCatalog
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateBind
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyAggregateMetadata ConstructiveConstAggregateBuilders

theorem struct_bind (c : context) (x : Nat) (k : structtype → Plan SpecTecRequest) (n finish : Nat) (value : Value)
    (h : Eval SpecTec.specTecProgram (.bind (.call ⟨structtype,SpecTecCall.«$struct_type» c x⟩) k) n (.success value) finish) :
    ∃s : StructIndex c,s.index=x ∧ Eval SpecTec.specTecProgram (k (.StructT s.fields)) n (.success value) finish := by
  cases h with | bind_success hs tail =>
    rename_i middle st
    cases st with | StructT fields =>
      obtain ⟨hr,hn⟩ := (StructTypeDecision.struct_type_success_iff_result c x (.StructT fields) n middle).1 hs
      subst middle
      obtain ⟨s,hx,hf⟩ := structResult_inverse c x fields hr
      exact ⟨s,hx,by simpa only [hf] using tail⟩

theorem array_bind (c : context) (x : Nat) (k : arraytype → Plan SpecTecRequest) (n finish : Nat) (value : Value)
    (h : Eval SpecTec.specTecProgram (.bind (.call ⟨arraytype,SpecTecCall.«$array_type» c x⟩) k) n (.success value) finish) :
    ∃a : ArrayIndex c,a.index=x ∧ Eval SpecTec.specTecProgram (k (.ArrayT a.field)) n (.success value) finish := by
  cases h with | bind_success hs tail =>
    rename_i middle atype
    cases atype with | ArrayT field =>
      obtain ⟨hr,hn⟩ := (ArrayTypeDecision.array_type_success_iff_result c x (.ArrayT field) n middle).1 hs
      subst middle
      obtain ⟨a,hx,hf⟩ := arrayResult_inverse c x field hr
      exact ⟨a,hx,by simpa only [hf] using tail⟩

#print axioms array_bind
end properties.wasm_module_ok.ConstructiveBodyAggregateBind
