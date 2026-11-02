import properties.wasm_module_ok.ConstructiveTypeCopyExact
import properties.wasm_module_ok.CandidateSourceChecks
import properties.wasm_module_ok.RectypeLengthValidation
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeCopySource
open SpecTec properties.wasm_module_ok
open properties.wasm_module_ok.ConstructiveTypeCopy

/-- Source classifiers occur only in proofs, never in the generator. -/
theorem heap_bound (c : context) (ht : heaptype) :
    HeaptypeValidation.heaptypeValid c ht = true ↔ HeapBound c.TYPES.length ht := by
  cases ht <;> simp [HeaptypeValidation.heaptypeValid,HeapBound]
  case VarHT tv => cases tv <;> simp [HeaptypeValidation.heaptypeValid,HeapBound]

theorem val_bound (c : context) (vt : valtype)
    (h : ValtypeValidation.valtypeValid c vt = true) : ValBound c.TYPES.length vt := by
  cases vt <;> try trivial
  case RefT rt =>
    cases rt with
    | «% %» nu ht => exact (heap_bound c ht).1 h

theorem storage_bound (c : context) (st : storagetype)
    (h : StoragetypeValidation.storagetypeValid c st = true) : StorageBound c.TYPES.length st := by
  cases st with
  | ValStorageT vt => exact val_bound c vt h
  | PackStorageT pt => trivial

theorem field_bound (c : context) (ft : fieldtype)
    (h : FieldtypeValidation.fieldtypeValid c ft = true) : FieldBound c.TYPES.length ft := by
  cases ft with
  | FieldT mu st => exact storage_bound c st h

@[simp] theorem vals_valid (c : context) (ts : List valtype) :
    ResulttypeListValidation.allValtypesValid c ts = true ↔
      ∀ t ∈ ts, ValtypeValidation.valtypeValid c t = true := by
  induction ts <;> simp_all [ResulttypeListValidation.allValtypesValid]

@[simp] theorem fields_valid (c : context) (fs : List fieldtype) :
    StructtypeFieldListValidation.allFieldsValid c fs = true ↔
      ∀ f ∈ fs, FieldtypeValidation.fieldtypeValid c f = true := by
  induction fs <;> simp_all [StructtypeFieldListValidation.allFieldsValid]

@[simp] theorem heaps_valid (c : context) (hs : List heaptype) :
    SubtypeHeadListValidation.allHeaptypesValid c hs = true ↔
      ∀ h ∈ hs, HeaptypeValidation.heaptypeValid c h = true := by
  induction hs <;> simp_all [SubtypeHeadListValidation.allHeaptypesValid]

@[simp] theorem subs_valid (c : context) (ss : List SpecTec.subtype) :
    CandidateSourceChecks.sourceChecks c ss = true ↔
      ∀ s ∈ ss, SubtypeValidation.subtypeValid c s = true := by
  induction ss <;> simp_all [CandidateSourceChecks.sourceChecks]

theorem str_bound (c : context) (st : strtype)
    (h : StrtypeValidation.strtypeValid c st = true) : StrBound c.TYPES.length st := by
  cases st with
  | DefStructT st =>
    rcases st with ⟨fs⟩
    exact fun f hf => field_bound c f ((fields_valid c fs).1 h f hf)
  | DefArrayT ar =>
    rcases ar with ⟨f⟩
    exact field_bound c f h
  | DefFuncT ft =>
    rcases ft with ⟨ins,outs⟩
    have hh : ResulttypeListValidation.allValtypesValid c ins = true ∧
        ResulttypeListValidation.allValtypesValid c outs = true := by
      simpa [StrtypeValidation.strtypeValid,FunctypeValidation.functypeValid,
        FunctypeValidation.resulttypeValid] using h
    exact ⟨fun t ht => val_bound c t ((vals_valid c ins).1 hh.1 t ht),
      fun t ht => val_bound c t ((vals_valid c outs).1 hh.2 t ht)⟩

theorem sub_bound (c : context) (st : SpecTec.subtype)
    (h : SubtypeValidation.subtypeValid c st = true) : SubBound c.TYPES.length st := by
  rcases st with ⟨fin,hs,st⟩
  have hh : (hs.length ≤ 1 ∧ SubtypeHeadListValidation.allHeaptypesValid c hs = true) ∧
      StrtypeValidation.strtypeValid c st = true := by
    simpa [SubtypeValidation.subtypeValid] using h
  exact ⟨fun ht hm => (heap_bound c ht).1 ((heaps_valid c hs).1 hh.1.2 ht hm),
    str_bound c st hh.2⟩

theorem group_bound (c : context) (ss : List SpecTec.subtype)
    (h : CandidateSourceChecks.sourceChecks c ss = true) : GroupBound c.TYPES.length ss :=
  fun s hs => sub_bound c s ((subs_valid c ss).1 h s hs)

/-- Every original successful recursive group supplies the reifier domain.
This is backward coverage, not a soundness assumption on a generated group. -/
theorem original_bound (before after : context) (ss : List SpecTec.subtype) (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨context,SpecTec.SpecTecCall.Rectype_ok before (.RecT ss)⟩)
      start (.success (.of after)) finish) : GroupBound (before.TYPES.length+ss.length) ss := by
  have hc := CandidateRectypeTable.rectype_success_candidateContext before after ss start finish h
  have hb := group_bound after ss
    (CandidateSourceChecks.rectype_success_sourceChecks before after after ss start finish h hc)
  obtain ⟨dts,rfl,hlen⟩ := RectypeLengthValidation.rectype_ok_appended_types_length
    before after ss start finish h
  simpa [hlen] using hb

#print axioms original_bound
end properties.wasm_module_ok.ConstructiveTypeCopySource
