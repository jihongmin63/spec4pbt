import properties.wasm_module_ok.ImportsValidation
import properties.wasm_module_ok.FuncsValidation
import properties.wasm_module_ok.MemsValidation
import properties.wasm_module_ok.TagsValidation
import properties.wasm_module_ok.CandidateTypesDecision

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructivePreludeRefs
open SpecTec SpecTecExecution properties.wasm_module_ok

def replace (refs : SpecTec.free) (c : context) : context := {c with REFS := refs}

@[simp] theorem replace_types (refs : SpecTec.free) (c : context) :
    (replace refs c).TYPES = c.TYPES := rfl

theorem globaltype_replace (refs : SpecTec.free) (c : context) (gt : globaltype) :
    GlobaltypeValidation.globaltypeValid (replace refs c) gt =
      GlobaltypeValidation.globaltypeValid c gt := by
  cases gt
  rfl

theorem tabletype_replace (refs : SpecTec.free) (c : context) (tt : tabletype) :
    TabletypeValidation.tabletypeValid (replace refs c) tt =
      TabletypeValidation.tabletypeValid c tt := by
  cases tt with
  | TableT addr lim rt => cases addr <;> rfl

theorem func_decl_replace (refs : SpecTec.free) (c : context) (f : SpecTec.func) :
    FuncDeclValidation.funcDeclResult (replace refs c) f =
      (FuncDeclValidation.funcDeclResult c f).map (replace refs) := by
  cases h : c.TYPES[f.FTYPE]? with
  | none => simp [FuncDeclValidation.funcDeclResult, replace, h]
  | some dt =>
    cases hf : UnrollInterface.deftypeFunctype dt <;>
      simp [FuncDeclValidation.funcDeclResult, replace, h, hf]

theorem mem_decl_replace (refs : SpecTec.free) (c : context) (m : memory) :
    MemsValidation.memDeclResult (replace refs c) m =
      (MemsValidation.memDeclResult c m).map (replace refs) := by
  unfold MemsValidation.memDeclResult
  split <;> rfl

theorem tag_decl_replace (refs : SpecTec.free) (c : context) (t : tag) :
    TagsValidation.tagDeclResult (replace refs c) t =
      (TagsValidation.tagDeclResult c t).map (replace refs) := by
  cases h : c.TYPES[t.TGTYPE]? with
  | none => simp [TagsValidation.tagDeclResult, replace, h]
  | some dt =>
    unfold TagsValidation.tagDeclResult
    simp only [replace, h]
    split <;> rfl

theorem import_decl_replace (refs : SpecTec.free) (c : context) (i : SpecTec.«import») :
    ImportValidation.importDeclResult (replace refs c) i =
      (ImportValidation.importDeclResult c i).map (replace refs) := by
  cases i with
  | mk modname itemname d =>
    cases d with
    | FuncImport x =>
      cases h : c.TYPES[x]? with
      | none => simp [ImportValidation.importDeclResult, ImportValidation.funcImportResult, replace, h]
      | some dt =>
        unfold ImportValidation.importDeclResult ImportValidation.funcImportResult
        simp only [replace, h]
        split <;> rfl
    | TagImport x =>
      cases h : c.TYPES[x]? with
      | none => simp [ImportValidation.importDeclResult, ImportValidation.tagImportResult, replace, h]
      | some dt =>
        unfold ImportValidation.importDeclResult ImportValidation.tagImportResult
        simp only [replace, h]
        split <;> rfl
    | GlobalImport gt =>
      simp only [ImportValidation.importDeclResult, globaltype_replace]
      split <;> rfl
    | TableImport tt =>
      simp only [ImportValidation.importDeclResult, tabletype_replace]
      split <;> rfl
    | MemImport mt =>
      simp only [ImportValidation.importDeclResult]
      split <;> rfl

theorem imports_result_replace (refs : SpecTec.free) (c : context) (xs : List SpecTec.«import») :
    ImportsValidation.importsResult (replace refs c) xs =
      (ImportsValidation.importsResult c xs).map (replace refs) := by
  induction xs generalizing c with
  | nil => rfl
  | cons i xs ih =>
    simp only [ImportsValidation.importsResult, import_decl_replace]
    cases ImportValidation.importDeclResult c i <;> simp [ih]

theorem funcs_result_replace (refs : SpecTec.free) (c : context) (xs : List SpecTec.func) :
    FuncsValidation.funcsResult (replace refs c) xs =
      (FuncsValidation.funcsResult c xs).map (replace refs) := by
  induction xs generalizing c with
  | nil => rfl
  | cons f xs ih =>
    simp only [FuncsValidation.funcsResult, func_decl_replace]
    cases FuncDeclValidation.funcDeclResult c f <;> simp [ih]

theorem mems_result_replace (refs : SpecTec.free) (c : context) (xs : List memory) :
    MemsValidation.memsResult (replace refs c) xs =
      (MemsValidation.memsResult c xs).map (replace refs) := by
  induction xs generalizing c with
  | nil => rfl
  | cons m xs ih =>
    simp only [MemsValidation.memsResult, mem_decl_replace]
    cases MemsValidation.memDeclResult c m <;> simp [ih]

theorem tags_result_replace (refs : SpecTec.free) (c : context) (xs : List tag) :
    TagsValidation.tagsResult (replace refs c) xs =
      (TagsValidation.tagsResult c xs).map (replace refs) := by
  induction xs generalizing c with
  | nil => rfl
  | cons t xs ih =>
    simp only [TagsValidation.tagsResult, tag_decl_replace]
    cases TagsValidation.tagDeclResult c t <;> simp [ih]

theorem imports_replace (refs : SpecTec.free) (c result : context)
    (xs : List SpecTec.«import») (start finish : Nat)
    (h : Eval specTecProgram (.call ⟨context, SpecTecCall.Imports_ok c xs⟩)
      start (.success (.of result)) finish) :
    Eval specTecProgram (.call ⟨context, SpecTecCall.Imports_ok (replace refs c) xs⟩)
      start (.success (.of (replace refs result))) finish := by
  rw [ImportsValidation.imports_success_iff_result] at h ⊢
  exact ⟨by rw [imports_result_replace, h.1]; rfl, h.2⟩

theorem funcs_replace (refs : SpecTec.free) (c result : context)
    (xs : List SpecTec.func) (start finish : Nat)
    (h : Eval specTecProgram (.call ⟨context, SpecTecCall.Funcs_ok c xs⟩)
      start (.success (.of result)) finish) :
    Eval specTecProgram (.call ⟨context, SpecTecCall.Funcs_ok (replace refs c) xs⟩)
      start (.success (.of (replace refs result))) finish := by
  rw [FuncsValidation.funcs_success_iff_result] at h ⊢
  exact ⟨by rw [funcs_result_replace, h.1]; rfl, h.2⟩

theorem mems_replace (refs : SpecTec.free) (c result : context)
    (xs : List memory) (start finish : Nat)
    (h : Eval specTecProgram (.call ⟨context, SpecTecCall.Mems_ok c xs⟩)
      start (.success (.of result)) finish) :
    Eval specTecProgram (.call ⟨context, SpecTecCall.Mems_ok (replace refs c) xs⟩)
      start (.success (.of (replace refs result))) finish := by
  rw [MemsValidation.mems_success_iff_result] at h ⊢
  exact ⟨by rw [mems_result_replace, h.1]; rfl, h.2⟩

theorem tags_replace (refs : SpecTec.free) (c result : context)
    (xs : List tag) (start finish : Nat)
    (h : Eval specTecProgram (.call ⟨context, SpecTecCall.Tags_ok c xs⟩)
      start (.success (.of result)) finish) :
    Eval specTecProgram (.call ⟨context, SpecTecCall.Tags_ok (replace refs c) xs⟩)
      start (.success (.of (replace refs result))) finish := by
  rw [TagsValidation.tags_success_iff_result] at h ⊢
  exact ⟨by rw [tags_result_replace, h.1]; rfl, h.2⟩

theorem candidate_context_replace (refs : SpecTec.free) (c : context)
    (sts : List SpecTec.subtype) :
    CandidateRectypeTable.candidateContext (replace refs c) sts =
      (CandidateRectypeTable.candidateContext c sts).map (replace refs) := by
  have ht : CandidateRectypeTable.transformed (replace refs c) sts =
      CandidateRectypeTable.transformed c sts := rfl
  simp only [CandidateRectypeTable.candidateContext, ht]
  cases CandidateRectypeTable.transformed c sts <;> rfl

private theorem heaps_replace (refs : SpecTec.free) (c : context) (xs : List heaptype) :
    SubtypeHeadListValidation.allHeaptypesValid (replace refs c) xs =
      SubtypeHeadListValidation.allHeaptypesValid c xs := by
  have h : HeaptypeValidation.heaptypeValid (replace refs c) = HeaptypeValidation.heaptypeValid c := rfl
  induction xs <;> simp_all [SubtypeHeadListValidation.allHeaptypesValid]

private theorem vals_replace (refs : SpecTec.free) (c : context) (xs : List valtype) :
    ResulttypeListValidation.allValtypesValid (replace refs c) xs =
      ResulttypeListValidation.allValtypesValid c xs := by
  have h : ValtypeValidation.valtypeValid (replace refs c) = ValtypeValidation.valtypeValid c := rfl
  induction xs <;> simp_all [ResulttypeListValidation.allValtypesValid]

private theorem fields_replace (refs : SpecTec.free) (c : context) (xs : List fieldtype) :
    StructtypeFieldListValidation.allFieldsValid (replace refs c) xs =
      StructtypeFieldListValidation.allFieldsValid c xs := by
  have h : FieldtypeValidation.fieldtypeValid (replace refs c) = FieldtypeValidation.fieldtypeValid c := rfl
  induction xs <;> simp_all [StructtypeFieldListValidation.allFieldsValid]

private theorem strtype_replace (refs : SpecTec.free) (c : context) (st : strtype) :
    StrtypeValidation.strtypeValid (replace refs c) st = StrtypeValidation.strtypeValid c st := by
  cases st with
  | DefStructT st => cases st; exact fields_replace refs c _
  | DefArrayT arr => rfl
  | DefFuncT ft =>
    cases ft
    simp only [StrtypeValidation.strtypeValid, FunctypeValidation.functypeValid,
      FunctypeValidation.resulttypeValid, vals_replace]

private theorem subtype_replace (refs : SpecTec.free) (c : context) (st : SpecTec.subtype) :
    SubtypeValidation.subtypeValid (replace refs c) st = SubtypeValidation.subtypeValid c st := by
  cases st
  simp only [SubtypeValidation.subtypeValid, heaps_replace, strtype_replace]

theorem source_checks_replace (refs : SpecTec.free) (c : context) (sts : List SpecTec.subtype) :
    CandidateSourceChecks.sourceChecks (replace refs c) sts =
      CandidateSourceChecks.sourceChecks c sts := by
  induction sts <;> simp_all [CandidateSourceChecks.sourceChecks, subtype_replace]

private theorem match_fuel_replace (refs : SpecTec.free) (c : context) (fuel p q : Nat) :
    ValidatedMatchIndexFuel.matchIndexFuel (replace refs c) fuel p q =
      ValidatedMatchIndexFuel.matchIndexFuel c fuel p q := by
  induction fuel generalizing p q with
  | zero => rfl
  | succ fuel ih =>
    simp only [ValidatedMatchIndexFuel.matchIndexFuel, replace_types, ih]
    rfl

private theorem heap_match_replace (refs : SpecTec.free) (c : context) (a b : heaptype) :
    ReadyHeapMatch.readyHeapMatch (replace refs c) a b = ReadyHeapMatch.readyHeapMatch c a b := by
  have hm : ValidatedMatchIndexFuel.matchIndex (replace refs c) =
      ValidatedMatchIndexFuel.matchIndex c := by
    funext p q
    exact match_fuel_replace refs c (p + 1) p q
  simp only [ReadyHeapMatch.readyHeapMatch, ReadyHeapMatch.indexedValue,
    ReadyHeapMatchIndexed.indexedHeapMatch, ReadyMatchHeaptypeIndex.indexedDefMatch,
    replace_types, hm]

private theorem super_check_replace (refs : SpecTec.free) (c : context) (x : Nat)
    (st : strtype) (ht : heaptype) :
    CandidateStaticSuperCheck.staticSuperCheck (replace refs c) x st ht =
      CandidateStaticSuperCheck.staticSuperCheck c x st ht := by
  simp only [CandidateStaticSuperCheck.staticSuperCheck, ReadyStaticSubtypeMatch.staticSuperMatch,
    replace_types, heap_match_replace]

private theorem super_checks_replace (refs : SpecTec.free) (c : context) (x : Nat)
    (st : strtype) (hts : List heaptype) :
    CandidateStaticSuperList.staticSuperChecks (replace refs c) x st hts =
      CandidateStaticSuperList.staticSuperChecks c x st hts := by
  induction hts <;> simp_all [CandidateStaticSuperList.staticSuperChecks, super_check_replace]

theorem paired_checks_replace (refs : SpecTec.free) (c : context) (base : Nat)
    (ns : List Nat) (sts : List SpecTec.subtype) :
    CandidateGroupSuperChecks.pairedChecks (replace refs c) base ns sts =
      CandidateGroupSuperChecks.pairedChecks c base ns sts := by
  induction ns generalizing sts with
  | nil => cases sts <;> rfl
  | cons n ns ih =>
    cases sts with
    | nil => rfl
    | cons st sts =>
      cases st
      simp only [CandidateGroupSuperChecks.pairedChecks, super_checks_replace, ih]

theorem rectype_passes_replace (refs : SpecTec.free) (c : context)
    (sts : List SpecTec.subtype) :
    CandidateRectypeDecision.rectypePasses (replace refs c) sts =
      CandidateRectypeDecision.rectypePasses c sts := by
  simp only [CandidateRectypeDecision.rectypePasses, candidate_context_replace]
  cases CandidateRectypeTable.candidateContext c sts with
  | none => rfl
  | some d =>
    simp only [Option.map_some, source_checks_replace, paired_checks_replace]
    rfl

theorem types_result_replace (refs : SpecTec.free) (c : context) (ts : List SpecTec.type) :
    CandidateTypesDecision.typesResult (replace refs c) ts =
      (CandidateTypesDecision.typesResult c ts).map (replace refs) := by
  induction ts generalizing c with
  | nil => rfl
  | cons t ts ih =>
    cases t with
    | RecT sts =>
      simp only [CandidateTypesDecision.typesResult, rectype_passes_replace,
        candidate_context_replace]
      cases CandidateRectypeDecision.rectypePasses c sts <;> simp only [ Bool.false_eq_true, if_false, if_true]
      · rfl
      · cases CandidateRectypeTable.candidateContext c sts <;> simp [ih]

theorem validated_types_replace (refs : SpecTec.free) (c : context)
    (hc : ValidatedTypeChain.ValidatedTypes c) :
    ValidatedTypeChain.ValidatedTypes (replace refs c) := by
  induction hc with
  | seed d hd => exact .seed (replace refs d) hd
  | append before after sts start finish hb hrect ih =>
    obtain ⟨hp, ht⟩ := CandidateRectypeStep.passes_of_success before after sts start finish hb hrect
    have hr := CandidateRectypeStep.success_of_passes
      (replace refs before) (replace refs after) sts start ih
      (by rw [rectype_passes_replace]; exact hp)
      (by rw [candidate_context_replace, ht]; rfl)
    exact .append (replace refs before) (replace refs after) sts start start ih hr

/-- Type-stage transport assumes only the previously validated type prefix,
which the initial empty context and each earlier Types_ok stage establish. -/
theorem types_replace (refs : SpecTec.free) (c result : context)
    (ts : List SpecTec.type) (start finish : Nat)
    (hc : ValidatedTypeChain.ValidatedTypes c)
    (h : Eval specTecProgram (.call ⟨context, SpecTecCall.Types_ok c ts⟩)
      start (.success (.of result)) finish) :
    Eval specTecProgram (.call ⟨context, SpecTecCall.Types_ok (replace refs c) ts⟩)
      start (.success (.of (replace refs result))) finish := by
  have hr := CandidateTypesDecision.types_result_of_success c result ts start finish hc h
  have he := CandidateTypesDecision.types_success_of_result c result ts start hc hr
  have hdet : PrimitiveDeterministic specTecProgram := by intro req a b hp; cases hp
  have hn := (eval_deterministic hdet h he).2
  rw [hn]
  exact CandidateTypesDecision.types_success_of_result
    (replace refs c) (replace refs result) ts start (validated_types_replace refs c hc)
    (by rw [types_result_replace, hr]; rfl)

end properties.wasm_module_ok.ConstructivePreludeRefs
