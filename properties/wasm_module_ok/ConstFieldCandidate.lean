import properties.wasm_module_ok.ConstBasicInputCandidate
import properties.wasm_module_ok.StructExplicitFieldsDecision
import properties.wasm_module_ok.StructTypeDecision
import properties.wasm_module_ok.ArrayTypeDecision
import properties.wasm_module_ok.ConstStructExplicitDispatch
import properties.wasm_module_ok.ConstArrayExplicitDispatch
import properties.wasm_module_ok.ConstArrayFixedDispatch
import properties.wasm_module_ok.ConstArrayImplicitDispatch

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstFieldCandidate

/-- Inputs produced by expanding each indexed structure type in the context. -/
def structFieldCandidates (c : SpecTec.context) : List SpecTec.valtype :=
  (List.range c.TYPES.length).flatMap fun x =>
    match StructTypeDecision.structTypeResult c x with
    | some (.StructT fields) =>
        StructExplicitFieldsDecision.structFieldInputs fields
    | none => []

/-- Inputs produced by expanding each indexed array type in the context. -/
def arrayFieldCandidates (c : SpecTec.context) : List SpecTec.valtype :=
  (List.range c.TYPES.length).flatMap fun x =>
    match ArrayTypeDecision.arrayTypeResult c x with
    | some (.ArrayT field) => [UnpackedFieldDecision.unpackedFieldResult field]
    | none => []

def extendedCandidateTypes (c : SpecTec.context) : List SpecTec.valtype :=
  FiniteValidTypes.candidateTypes c ++
    structFieldCandidates c ++ arrayFieldCandidates c

def extendedCandidateUniverse (c : SpecTec.context) : Finset SpecTec.valtype :=
  (extendedCandidateTypes c).toFinset

theorem old_candidate_mem_extended
    (c : SpecTec.context) (t : SpecTec.valtype)
    (h : t ∈ FiniteValidTypes.candidateUniverse c) :
    t ∈ extendedCandidateUniverse c := by
  simp only [FiniteValidTypes.candidateUniverse, List.mem_toFinset] at h
  simp only [extendedCandidateUniverse, List.mem_toFinset,
    extendedCandidateTypes, List.mem_append]
  exact Or.inl (Or.inl h)

theorem struct_field_mem_extended
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (fields : List SpecTec.fieldtype) (t : SpecTec.valtype)
    (hbound : x < c.TYPES.length)
    (hstruct : StructTypeDecision.structTypeResult c x =
      some (.StructT fields))
    (hmem : t ∈ StructExplicitFieldsDecision.structFieldInputs fields) :
    t ∈ extendedCandidateUniverse c := by
  have hscan : t ∈ structFieldCandidates c := by
    simp only [structFieldCandidates, List.mem_flatMap]
    exact ⟨x, List.mem_range.mpr hbound, by simp [hstruct, hmem]⟩
  simp only [extendedCandidateUniverse, List.mem_toFinset,
    extendedCandidateTypes, List.mem_append]
  exact Or.inl (Or.inr hscan)

theorem array_field_mem_extended
    (c : SpecTec.context) (x : SpecTec.typeidx)
    (field : SpecTec.fieldtype)
    (hbound : x < c.TYPES.length)
    (harray : ArrayTypeDecision.arrayTypeResult c x =
      some (.ArrayT field)) :
    UnpackedFieldDecision.unpackedFieldResult field ∈
      extendedCandidateUniverse c := by
  have hscan : UnpackedFieldDecision.unpackedFieldResult field ∈
      arrayFieldCandidates c := by
    simp only [arrayFieldCandidates, List.mem_flatMap]
    exact ⟨x, List.mem_range.mpr hbound, by simp [harray]⟩
  simp only [extendedCandidateUniverse, List.mem_toFinset,
    extendedCandidateTypes, List.mem_append]
  exact Or.inr hscan

theorem struct_new_explicit_inputs_extended
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«STRUCT.NEW» x .Explicit)⟩)
      start (.success (.of iit)) finish) :
    ∀ t ∈ iit.1.INS.2, t ∈ extendedCandidateUniverse c := by
  obtain ⟨fields, ts, dt, middle, hstruct, hfields, hget, hiit⟩ :=
    (ConstStructExplicitDispatch.struct_new_explicit_dispatch_iff
      c irt x iit start finish).1 hcall
  have hbound : x < c.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  have hstructResult : StructTypeDecision.structTypeResult c x =
      some (.StructT fields) :=
    ((StructTypeDecision.struct_type_success_iff_result
      c x (.StructT fields) start middle).1 hstruct).1
  have hts : ts = StructExplicitFieldsDecision.structFieldInputs fields :=
    ((StructExplicitFieldsDecision.fields_success_iff_inputs
      fields ts middle finish).1 hfields).1
  intro t hmem
  rw [hiit] at hmem
  change t ∈ ts at hmem
  rw [hts] at hmem
  exact struct_field_mem_extended c x fields t hbound hstructResult hmem

theorem array_new_explicit_inputs_extended
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW» x .Explicit)⟩)
      start (.success (.of iit)) finish) :
    ∀ t ∈ iit.1.INS.2, t ∈ extendedCandidateUniverse c := by
  obtain ⟨field, fieldType, dt, middle, harray, hunpack, hget, hiit⟩ :=
    (ConstArrayExplicitDispatch.array_new_explicit_dispatch_iff
      c irt x iit start finish).1 hcall
  have hbound : x < c.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  have harrayResult : ArrayTypeDecision.arrayTypeResult c x =
      some (.ArrayT field) :=
    ((ArrayTypeDecision.array_type_success_iff_result
      c x (.ArrayT field) start middle).1 harray).1
  have hfieldType : fieldType =
      UnpackedFieldDecision.unpackedFieldResult field :=
    ((UnpackedFieldDecision.unpacked_field_success_iff_result
      field fieldType middle finish).1 hunpack).1
  have hfieldCandidate : fieldType ∈ extendedCandidateUniverse c := by
    rw [hfieldType]
    exact array_field_mem_extended c x field hbound harrayResult
  have hi32 : SpecTec.valtype.NumT .I32T ∈
      extendedCandidateUniverse c :=
    old_candidate_mem_extended c _
      (FiniteValidTypes.valid_mem_candidateUniverse c _ (by rfl))
  intro t hmem
  rw [hiit] at hmem
  change t ∈ [fieldType, .NumT .I32T] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with heq | heq
  · cases heq; exact hfieldCandidate
  · cases heq; exact hi32

theorem mem_make_result_eq {X : Type} (value t : X)
    (count : Nat) (h : t ∈ MakeValidation.makeResult value count) :
    t = value := by
  induction count with
  | zero => cases h
  | succ count ih =>
    simp only [MakeValidation.makeResult, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with hprev | hlast
    · exact ih hprev
    · exact hlast

theorem array_new_fixed_inputs_extended
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (count : SpecTec.n)
    (iit : SpecTec.inferinstrtype) (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW_FIXED» x count)⟩)
      start (.success (.of iit)) finish) :
    ∀ t ∈ iit.1.INS.2, t ∈ extendedCandidateUniverse c := by
  obtain ⟨field, fieldType, dt, middle, harray, hunpack, hget, hiit⟩ :=
    (ConstArrayFixedDispatch.array_new_fixed_dispatch_iff
      c irt x count iit start finish).1 hcall
  have hbound : x < c.TYPES.length :=
    (List.getElem?_eq_some_iff.mp hget).1
  have harrayResult : ArrayTypeDecision.arrayTypeResult c x =
      some (.ArrayT field) :=
    ((ArrayTypeDecision.array_type_success_iff_result
      c x (.ArrayT field) start middle).1 harray).1
  have hfieldType : fieldType =
      UnpackedFieldDecision.unpackedFieldResult field :=
    ((UnpackedFieldDecision.unpacked_field_success_iff_result
      field fieldType middle finish).1 hunpack).1
  intro t hmem
  rw [hiit] at hmem
  change t ∈ MakeValidation.makeResult fieldType count at hmem
  have heq := mem_make_result_eq fieldType t count hmem
  cases heq
  rw [hfieldType]
  exact array_field_mem_extended c x field hbound harrayResult

theorem array_new_implicit_inputs_extended
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (x : SpecTec.typeidx) (iit : SpecTec.inferinstrtype)
    (start finish : Nat)
    (hcall : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.SpecTecCall.Instr_ok c irt (.«ARRAY.NEW» x .Implicit)⟩)
      start (.success (.of iit)) finish) :
    ∀ t ∈ iit.1.INS.2, t ∈ extendedCandidateUniverse c := by
  obtain ⟨field, fieldType, dt, middle, mid2,
    harray, hunpack, hdefault, hget, hiit⟩ :=
    (ConstArrayImplicitDispatch.array_new_implicit_dispatch_iff
      c irt x iit start finish).1 hcall
  have hi32 : SpecTec.valtype.NumT .I32T ∈
      extendedCandidateUniverse c :=
    old_candidate_mem_extended c _
      (FiniteValidTypes.valid_mem_candidateUniverse c _ (by rfl))
  intro t hmem
  rw [hiit] at hmem
  change t ∈ ([.NumT .I32T] : List SpecTec.valtype) at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  cases hmem
  exact hi32

end properties.wasm_module_ok.ConstFieldCandidate
