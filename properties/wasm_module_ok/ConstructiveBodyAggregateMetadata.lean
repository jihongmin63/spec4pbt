import properties.wasm_module_ok.ConstructiveBodyEnvironment
import properties.wasm_module_ok.ConstructiveBodyLookup
import properties.wasm_module_ok.ConstructiveConstSeedCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAggregateMetadata
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveConstAggregateBuilders

theorem structResult {c : context} (s : StructIndex c) : StructTypeDecision.structTypeResult c s.index=some (.StructT s.fields) := by
  simp [StructTypeDecision.structTypeResult,s.lookup,s.expansion]
theorem arrayResult {c : context} (a : ArrayIndex c) : ArrayTypeDecision.arrayTypeResult c a.index=some (.ArrayT a.field) := by
  simp [ArrayTypeDecision.arrayTypeResult,a.lookup,a.expansion]

theorem structCall {c : context} (s : StructIndex c) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨structtype,SpecTecCall.«$struct_type» c s.index⟩)
      n (.success (.of (structtype.StructT s.fields))) n :=
  (StructTypeDecision.struct_type_success_iff_result c s.index _ n n).2 ⟨structResult s,rfl⟩
theorem arrayCall {c : context} (a : ArrayIndex c) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram (.call ⟨arraytype,SpecTecCall.«$array_type» c a.index⟩)
      n (.success (.of (arraytype.ArrayT a.field))) n :=
  (ArrayTypeDecision.array_type_success_iff_result c a.index _ n n).2 ⟨arrayResult a,rfl⟩

theorem structRef {c : context} (s : StructIndex c) (nu : SpecTec.null) :
    CandidateValMatch.InTableVal c (.RefT (.«% %» nu (.DefHT s.definition))) :=
  CandidateValMembership.table_definition_in_table c s.definition (List.mem_of_getElem? s.lookup) nu
theorem arrayRef {c : context} (a : ArrayIndex c) (nu : SpecTec.null) :
    CandidateValMatch.InTableVal c (.RefT (.«% %» nu (.DefHT a.definition))) :=
  CandidateValMembership.table_definition_in_table c a.definition (List.mem_of_getElem? a.lookup) nu

theorem structInputs {c : context} (s : StructIndex c) (env : Env c) :
    ∀t∈StructExplicitFieldsDecision.structFieldInputs s.fields,CandidateValMatch.InTableVal c t :=
  fun t ht => ConstExtendedCandidateReady.struct_field_in_table c env.nested s.index s.fields t (structResult s) ht
theorem arrayInput {c : context} (a : ArrayIndex c) (env : Env c) :
    CandidateValMatch.InTableVal c (UnpackedFieldDecision.unpackedFieldResult a.field) :=
  ConstExtendedCandidateReady.array_field_in_table c env.nested a.index a.field (arrayResult a)

theorem structResult_inverse (c : context) (x : Nat) (fields : List fieldtype)
    (h : StructTypeDecision.structTypeResult c x=some (.StructT fields)) :
    ∃s : StructIndex c,s.index=x ∧ s.fields=fields := by
  unfold StructTypeDecision.structTypeResult at h
  cases hx : c.TYPES[x]? with
  | none => simp only [hx] at h; cases h
  | some dt =>
    simp only [hx] at h
    cases he : UnrollInterface.expandResult dt with
    | none => rw [he] at h; cases h
    | some st =>
      cases st with
      | DefFuncT f => rw [he] at h; cases h
      | DefArrayT a => rw [he] at h; cases h
      | DefStructT s =>
        cases s with | StructT fs =>
          rw [he] at h
          have hf : fs=fields := by simpa using h
          subst fs
          exact ⟨⟨x,dt,fields,hx,he⟩,rfl,rfl⟩

theorem arrayResult_inverse (c : context) (x : Nat) (field : fieldtype)
    (h : ArrayTypeDecision.arrayTypeResult c x=some (.ArrayT field)) :
    ∃a : ArrayIndex c,a.index=x ∧ a.field=field := by
  unfold ArrayTypeDecision.arrayTypeResult at h
  cases hx : c.TYPES[x]? with
  | none => simp only [hx] at h; cases h
  | some dt =>
    simp only [hx] at h
    cases he : UnrollInterface.expandResult dt with
    | none => rw [he] at h; cases h
    | some st =>
      cases st with
      | DefFuncT f => rw [he] at h; cases h
      | DefStructT s => rw [he] at h; cases h
      | DefArrayT a =>
        cases a with | ArrayT ft =>
          rw [he] at h
          have hf : ft=field := by simpa using h
          subst ft
          exact ⟨⟨x,dt,field,hx,he⟩,rfl,rfl⟩

#print axioms structResult_inverse
end properties.wasm_module_ok.ConstructiveBodyAggregateMetadata
