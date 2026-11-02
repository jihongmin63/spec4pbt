import properties.wasm_module_ok.ConstructiveModuleEnvironment
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveModuleImportEnvironment
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveModuleEnvironment

theorem valtype_backed (c : context) (t : valtype) (hv : ValtypeValidation.valtypeValid c t=true) :
    CandidateValMatch.InTableVal c t :=
  CandidateValMembership.valid_candidate_in_table c t ((FiniteValidTypes.validCandidates_spec c t).2 hv)

theorem one (c out : context) (env : Env c) (i : SpecTec.«import»)
    (h : ImportValidation.importDeclResult c i=some out) : Env out := by
  rcases i with ⟨modName,itemName,desc⟩
  cases desc with
  | MemImport mt =>
    cases hv : MemtypeValidation.memtypeValid mt with
    | false => simp [ImportValidation.importDeclResult,hv] at h
    | true =>
      have he : {c with MEMS:=c.MEMS++[mt]}=out := by simpa [ImportValidation.importDeclResult,hv] using h
      rw [←he]
      exact withMems c env _
  | GlobalImport gt =>
    cases gt with | GlobalT mu t =>
      cases hv : ValtypeValidation.valtypeValid c t with
      | false => simp [ImportValidation.importDeclResult,GlobaltypeValidation.globaltypeValid,hv] at h
      | true =>
        have he : {c with GLOBALS:=c.GLOBALS++[.GlobalT mu t]}=out := by
          simpa [ImportValidation.importDeclResult,GlobaltypeValidation.globaltypeValid,hv] using h
        rw [←he]
        apply withGlobals c env
        intro gt hg
        rcases List.mem_append.mp hg with hg|hg
        · exact env.provenance.globals gt hg
        · have he : gt=.GlobalT mu t := List.mem_singleton.mp hg
          subst gt
          exact valtype_backed c t hv
  | TableImport tt =>
    cases hv : TabletypeValidation.tabletypeValid c tt with
    | false => simp [ImportValidation.importDeclResult,hv] at h
    | true =>
      have he : {c with TABLES:=c.TABLES++[tt]}=out := by simpa [ImportValidation.importDeclResult,hv] using h
      rw [←he]
      apply withTables c env
      intro addr lim rt ht
      rcases List.mem_append.mp ht with ht|ht
      · exact env.tables addr lim rt ht
      · have he : tt=.TableT addr lim rt := (List.mem_singleton.mp ht).symm
        subst tt
        apply valtype_backed c (.RefT rt)
        cases rt with | «% %» nu heap =>
          cases addr <;> exact (Bool.and_eq_true_iff.mp hv).1
  | FuncImport x =>
    cases hx : c.TYPES[x]? with
    | none => simp [ImportValidation.importDeclResult,ImportValidation.funcImportResult,hx] at h
    | some dt =>
      cases hf : (UnrollInterface.deftypeFunctype dt).isSome with
      | false => simp [ImportValidation.importDeclResult,ImportValidation.funcImportResult,hx,hf] at h
      | true =>
        have he : {c with FUNCS:=c.FUNCS++[dt]}=out := by
          simpa [ImportValidation.importDeclResult,ImportValidation.funcImportResult,hx,hf] using h
        rw [←he]
        apply withFuncs c env
        intro d hd
        rcases List.mem_append.mp hd with hd|hd
        · exact env.provenance.funcs d hd
        · have he : d=dt := List.mem_singleton.mp hd
          subst d
          exact List.mem_iff_getElem?.mpr ⟨x,hx⟩
  | TagImport x =>
    cases hx : c.TYPES[x]? with
    | none => simp [ImportValidation.importDeclResult,ImportValidation.tagImportResult,hx] at h
    | some dt =>
      cases hv : TagtypeValidation.tagtypeValid (.TagT dt) with
      | false => simp [ImportValidation.importDeclResult,ImportValidation.tagImportResult,hx,hv] at h
      | true =>
        have he : {c with TAGS:=c.TAGS++[.TagT dt]}=out := by
          simpa [ImportValidation.importDeclResult,ImportValidation.tagImportResult,hx,hv] using h
        rw [←he]
        apply env.setTags
        intro d hd
        rcases List.mem_append.mp hd with hd|hd
        · exact env.tags d hd
        · have he : d=dt := by simpa using hd
          subst d
          exact List.mem_iff_getElem?.mpr ⟨x,hx⟩

theorem many (c out : context) (env : Env c) (items : List SpecTec.«import»)
    (h : ImportsValidation.importsResult c items=some out) : Env out := by
  induction items generalizing c with
  | nil => cases h; exact env
  | cons i items ih =>
    cases hi : ImportValidation.importDeclResult c i with
    | none => simp [ImportsValidation.importsResult,hi] at h
    | some next =>
      apply ih next (one c next env i hi)
      simpa only [ImportsValidation.importsResult,hi,Option.bind_some] using h

/-- The actual constructive import result establishes the next environment. -/
theorem generated (c : context) (env : Env c) (out : ConstructiveImports.Result c) : Env out.after :=
  many c out.after env out.items out.correct

#print axioms one
#print axioms generated
end properties.wasm_module_ok.ConstructiveModuleImportEnvironment
