import properties.wasm_module_ok.ConstFieldCandidate
import properties.wasm_module_ok.CandidateUniverseReady
import properties.wasm_module_ok.CandidateNestedReady
import properties.wasm_module_ok.ConstInputCoverage

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstExtendedCandidateReady

theorem unpacked_field_in_table
    (c : SpecTec.context) (field : SpecTec.fieldtype)
    (hfield : ∀ ht, ht ∈ ReadyMatchReachability.sourceFieldHeaptypes field →
      CandidateHeapMatch.InTable c ht) :
    CandidateValMatch.InTableVal c
      (UnpackedFieldDecision.unpackedFieldResult field) := by
  cases field with
  | FieldT m storage =>
    cases storage with
    | PackStorageT _ =>
      intro ht hmem
      cases hmem
    | ValStorageT t =>
      intro ht hmem
      exact hfield ht hmem

theorem expanded_source_in_table
    (c : SpecTec.context)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (x : Nat) (dt : SpecTec.deftype) (strt : SpecTec.strtype)
    (hget : c.TYPES[x]? = some dt)
    (hexpand : UnrollInterface.expandResult dt = some strt)
    (ht : SpecTec.heaptype)
    (hmem : ht ∈ ReadyMatchReachability.sourceHeaptypes strt) :
    CandidateHeapMatch.InTable c ht := by
  have hx : x < c.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  obtain ⟨dt', fin, supers, strt', hget', hunroll, hrefs⟩ :=
    (CandidateNestedReady.nestedTableReady_true_iff c).mp hnested x hx
  rw [hget] at hget'
  cases hget'
  have hstrt : strt' = strt := by
    simpa [UnrollInterface.expandResult, hunroll] using hexpand
  subst strt'
  rcases hrefs ht hmem with hbase | ⟨k, dtK, hlookup, heq⟩
  · exact .base ht hbase
  · subst ht
    exact .definition k dtK hlookup

theorem struct_field_in_table
    (c : SpecTec.context)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (x : SpecTec.typeidx) (fields : List SpecTec.fieldtype)
    (t : SpecTec.valtype)
    (hstruct : StructTypeDecision.structTypeResult c x =
      some (.StructT fields))
    (hmem : t ∈ StructExplicitFieldsDecision.structFieldInputs fields) :
    CandidateValMatch.InTableVal c t := by
  cases hget : c.TYPES[x]? with
  | none => simp [StructTypeDecision.structTypeResult, hget] at hstruct
  | some dt =>
    cases hexpand : UnrollInterface.expandResult dt with
    | none => simp [StructTypeDecision.structTypeResult, hget, hexpand] at hstruct
    | some strt =>
      cases strt with
      | DefFuncT ft =>
        simp [StructTypeDecision.structTypeResult, hget, hexpand] at hstruct
      | DefArrayT arr =>
        simp [StructTypeDecision.structTypeResult, hget, hexpand] at hstruct
      | DefStructT st =>
        cases st with
        | StructT actualFields =>
          have heq : actualFields = fields := by
            simpa [StructTypeDecision.structTypeResult, hget, hexpand]
              using hstruct
          subst actualFields
          obtain ⟨field, hfield, rfl⟩ :=
            List.mem_map.mp hmem
          apply unpacked_field_in_table c field
          intro ht hsource
          apply expanded_source_in_table c hnested x dt
            (.DefStructT (.StructT fields)) hget hexpand ht
          exact List.mem_flatMap.mpr ⟨field, hfield, hsource⟩

theorem array_field_in_table
    (c : SpecTec.context)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (x : SpecTec.typeidx) (field : SpecTec.fieldtype)
    (harray : ArrayTypeDecision.arrayTypeResult c x =
      some (.ArrayT field)) :
    CandidateValMatch.InTableVal c
      (UnpackedFieldDecision.unpackedFieldResult field) := by
  cases hget : c.TYPES[x]? with
  | none => simp [ArrayTypeDecision.arrayTypeResult, hget] at harray
  | some dt =>
    cases hexpand : UnrollInterface.expandResult dt with
    | none => simp [ArrayTypeDecision.arrayTypeResult, hget, hexpand] at harray
    | some strt =>
      cases strt with
      | DefFuncT ft =>
        simp [ArrayTypeDecision.arrayTypeResult, hget, hexpand] at harray
      | DefStructT st =>
        simp [ArrayTypeDecision.arrayTypeResult, hget, hexpand] at harray
      | DefArrayT arr =>
        cases arr with
        | ArrayT actualField =>
          have heq : actualField = field := by
            simpa [ArrayTypeDecision.arrayTypeResult, hget, hexpand]
              using harray
          subst actualField
          apply unpacked_field_in_table c field
          intro ht hsource
          exact expanded_source_in_table c hnested x dt
            (.DefArrayT (.ArrayT field)) hget hexpand ht hsource

theorem extended_candidate_in_table
    (c : SpecTec.context)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true)
    (t : SpecTec.valtype)
    (h : t ∈ ConstFieldCandidate.extendedCandidateUniverse c) :
    CandidateValMatch.InTableVal c t := by
  simp only [ConstFieldCandidate.extendedCandidateUniverse,
    List.mem_toFinset, ConstFieldCandidate.extendedCandidateTypes,
    List.mem_append] at h
  rcases h with (hold | hstruct) | harray
  · exact CandidateUniverseReady.candidate_universe_in_table c t hprov
      (by simpa [FiniteValidTypes.candidateUniverse] using hold)
  · obtain ⟨x, _, hx⟩ :=
      (List.mem_flatMap.mp hstruct)
    cases hresult : StructTypeDecision.structTypeResult c x with
    | none => simp [hresult] at hx
    | some st =>
      cases st with
      | StructT fields =>
        have hmem : t ∈
            StructExplicitFieldsDecision.structFieldInputs fields := by
          simpa [hresult] using hx
        exact struct_field_in_table c hnested x fields t hresult hmem
  · obtain ⟨x, _, hx⟩ :=
      (List.mem_flatMap.mp harray)
    cases hresult : ArrayTypeDecision.arrayTypeResult c x with
    | none => simp [hresult] at hx
    | some arr =>
      cases arr with
      | ArrayT field =>
        have heq : t =
            UnpackedFieldDecision.unpackedFieldResult field := by
          simpa [hresult] using hx
        subst t
        exact array_field_in_table c hnested x field hresult

theorem is_const_instruction_inputs_in_table
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (i : SpecTec.instr) (iit : SpecTec.inferinstrtype)
    (start middle finish : Nat)
    (hconst : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$is_const» c i⟩)
      start (.success (.of true)) middle)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt i⟩)
      middle (.success (.of iit)) finish)
    (hprov : CandidateUniverseReady.Provenance c)
    (hnested : CandidateNestedReady.nestedTableReady c = true) :
    ∀ t ∈ iit.1.INS.2, CandidateValMatch.InTableVal c t := by
  intro t ht
  exact extended_candidate_in_table c hprov hnested t
    (ConstInputCoverage.inputs_candidate_of_is_const
      c irt i iit start middle finish hconst hcall t ht)

theorem nested_table_ready_of_validated_types
    (c : SpecTec.context)
    (hvalid : ValidatedTypeChain.ValidatedTypes c) :
    CandidateNestedReady.nestedTableReady c = true := by
  apply (CandidateNestedReady.nestedTableReady_true_iff c).2
  intro p hp
  exact ValidatedNestedReferences.validated_type_unrolled_nested_references
    c p hvalid hp

end properties.wasm_module_ok.ConstExtendedCandidateReady
