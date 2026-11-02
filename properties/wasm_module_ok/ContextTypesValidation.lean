import properties.wasm_module_ok.ImportsValidation
import properties.wasm_module_ok.FuncHeadersStageGenerator
import properties.wasm_module_ok.MemsValidation
import properties.wasm_module_ok.TagsValidation
import properties.wasm_module_ok.HeaderBodyCompletion

set_option autoImplicit false

namespace properties.wasm_module_ok.ContextTypesValidation

theorem import_decl_types
    (c out : SpecTec.context) (i : SpecTec.«import»)
    (h : ImportValidation.importDeclResult c i = some out) :
    out.TYPES = c.TYPES := by
  cases i with
  | mk moduleName itemName desc =>
      cases desc with
      | FuncImport x =>
          simp only [ImportValidation.importDeclResult] at h
          unfold ImportValidation.funcImportResult at h
          cases hget : c.TYPES[x]? with
          | none => simp [hget] at h
          | some dt =>
              cases hv : (UnrollInterface.deftypeFunctype dt).isSome with
              | false => simp [hget, hv] at h
              | true =>
                  simp [hget, hv] at h
                  cases h
                  rfl
      | GlobalImport gt =>
          cases hv : GlobaltypeValidation.globaltypeValid c gt with
          | false => simp [ImportValidation.importDeclResult, hv] at h
          | true =>
              simp [ImportValidation.importDeclResult, hv] at h
              cases h
              rfl
      | TableImport tt =>
          cases hv : TabletypeValidation.tabletypeValid c tt with
          | false => simp [ImportValidation.importDeclResult, hv] at h
          | true =>
              simp [ImportValidation.importDeclResult, hv] at h
              cases h
              rfl
      | MemImport mt =>
          cases hv : MemtypeValidation.memtypeValid mt with
          | false => simp [ImportValidation.importDeclResult, hv] at h
          | true =>
              simp [ImportValidation.importDeclResult, hv] at h
              cases h
              rfl
      | TagImport x =>
          simp only [ImportValidation.importDeclResult] at h
          unfold ImportValidation.tagImportResult at h
          cases hget : c.TYPES[x]? with
          | none => simp [hget] at h
          | some dt =>
              cases hv : TagtypeValidation.tagtypeValid (.TagT dt) with
              | false => simp [hget, hv] at h
              | true =>
                  simp [hget, hv] at h
                  cases h
                  rfl

theorem imports_types
    (c out : SpecTec.context) (is : List SpecTec.«import»)
    (h : ImportsValidation.importsResult c is = some out) :
    out.TYPES = c.TYPES := by
  induction is generalizing c with
  | nil =>
      simp [ImportsValidation.importsResult] at h
      cases h
      rfl
  | cons i is ih =>
      simp only [ImportsValidation.importsResult] at h
      cases hhead : ImportValidation.importDeclResult c i with
      | none => simp [hhead] at h
      | some c₁ =>
          simp only [hhead, Option.bind_some] at h
          exact (ih c₁ h).trans (import_decl_types c c₁ i hhead)

theorem headers_types
    (c out : SpecTec.context) (xs : List SpecTec.typeidx)
    (h : FuncHeadersStageGenerator.headerResult c xs = some out) :
    out.TYPES = c.TYPES :=
  HeaderBodyCompletion.header_result_types c out xs h

theorem mem_decl_types
    (c out : SpecTec.context) (m : SpecTec.memory)
    (h : MemsValidation.memDeclResult c m = some out) :
    out.TYPES = c.TYPES := by
  unfold MemsValidation.memDeclResult at h
  cases hv : MemtypeValidation.memtypeValid m.MTYPE with
  | false => simp [hv] at h
  | true =>
      simp [hv] at h
      cases h
      rfl

theorem mems_types
    (c out : SpecTec.context) (ms : List SpecTec.memory)
    (h : MemsValidation.memsResult c ms = some out) :
    out.TYPES = c.TYPES := by
  induction ms generalizing c with
  | nil =>
      simp [MemsValidation.memsResult] at h
      cases h
      rfl
  | cons m ms ih =>
      simp only [MemsValidation.memsResult] at h
      cases hhead : MemsValidation.memDeclResult c m with
      | none => simp [hhead] at h
      | some c₁ =>
          simp only [hhead, Option.bind_some] at h
          exact (ih c₁ h).trans (mem_decl_types c c₁ m hhead)

theorem tag_decl_types
    (c out : SpecTec.context) (t : SpecTec.tag)
    (h : TagsValidation.tagDeclResult c t = some out) :
    out.TYPES = c.TYPES := by
  unfold TagsValidation.tagDeclResult at h
  cases hget : c.TYPES[t.TGTYPE]? with
  | none => simp [hget] at h
  | some dt =>
      cases hv : TagtypeValidation.tagtypeValid (.TagT dt) with
      | false => simp [hget, hv] at h
      | true =>
          simp [hget, hv] at h
          cases h
          rfl

theorem tags_types
    (c out : SpecTec.context) (ts : List SpecTec.tag)
    (h : TagsValidation.tagsResult c ts = some out) :
    out.TYPES = c.TYPES := by
  induction ts generalizing c with
  | nil =>
      simp [TagsValidation.tagsResult] at h
      cases h
      rfl
  | cons t ts ih =>
      simp only [TagsValidation.tagsResult] at h
      cases hhead : TagsValidation.tagDeclResult c t with
      | none => simp [hhead] at h
      | some c₁ =>
          simp only [hhead, Option.bind_some] at h
          exact (ih c₁ h).trans (tag_decl_types c c₁ t hhead)

end properties.wasm_module_ok.ContextTypesValidation
