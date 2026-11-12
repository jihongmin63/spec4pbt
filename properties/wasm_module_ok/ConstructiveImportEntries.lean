import properties.wasm_module_ok.ConstructiveImportTypes
import properties.wasm_module_ok.ConstructiveAttach
import properties.wasm_module_ok.ConstructiveConstTableCore

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveImportEntries
open SpecTec properties.wasm_module_ok
open ConstructiveImportTypes ConstructiveConstTableCore

structure Entry (c : context) where
  descriptor : importdesc
  output : context
  correct : ∀ modName itemName : SpecTec.name,
    ImportValidation.importDeclResult c ⟨modName,itemName,descriptor⟩ = some output

def memoryEntry (c : context) (mt : {mt : memtype // MemtypeValidation.memtypeValid mt = true}) : Entry c :=
  ⟨.MemImport mt.val,{c with MEMS := c.MEMS ++ [mt.val]},by
    intro m n; simp [ImportValidation.importDeclResult,mt.property]⟩
def globalEntry (c : context) (gt : {gt : globaltype // GlobaltypeValidation.globaltypeValid c gt = true}) : Entry c :=
  ⟨.GlobalImport gt.val,{c with GLOBALS := c.GLOBALS ++ [gt.val]},by
    intro m n; simp [ImportValidation.importDeclResult,gt.property]⟩
def tableEntry (c : context) (tt : {tt : tabletype // TabletypeValidation.tabletypeValid c tt = true}) : Entry c :=
  ⟨.TableImport tt.val,{c with TABLES := c.TABLES ++ [tt.val]},by
    intro m n; simp [ImportValidation.importDeclResult,tt.property]⟩
def functionEntry (c : context) (i : FunctionIndex c) : Entry c :=
  ⟨.FuncImport i.val.val,{c with FUNCS := c.FUNCS ++ [c.TYPES[i.val.val]]},by
    intro m n; exact function_result c i⟩
def tagEntry (c : context) (i : TagIndex c) : Entry c :=
  ⟨.TagImport i.val.val,{c with TAGS := c.TAGS ++ [.TagT c.TYPES[i.val.val]]},by
    intro m n; exact tag_result c i⟩

def memories (c : context) : Audited (Entry c) :=
  Audited.map (memoryEntry c)
    ⟨ConstructiveAttach.refine ConstructiveLimits.memories
      (ConstructiveGenAudit.finite_audit _ ConstructiveLimits.memories_finite) _
      (fun mt hm => (ConstructiveLimits.memories_support mt).1 hm),
     ConstructiveAttach.refine_audit _ _ _ _⟩
def globals (c : context) : Audited (Entry c) :=
  Audited.map (globalEntry c)
    ⟨ConstructiveAttach.refine (ConstructiveImportTypes.globals c)
      (ConstructiveGenAudit.finite_audit _ (globals_finite c)) _
      (fun gt hg => (globals_support c gt).1 hg),
     ConstructiveAttach.refine_audit _ _ _ _⟩
def tables (c : context) : Audited (Entry c) :=
  Audited.map (tableEntry c)
    ⟨ConstructiveAttach.refine (ConstructiveImportTypes.tables c)
      (ConstructiveGenAudit.finite_audit _ (tables_finite c)) _
      (fun tt ht => (tables_support c tt).1 ht),
     ConstructiveAttach.refine_audit _ _ _ _⟩

def alternatives (c : context) : List (Audited (Entry c)) :=
  [globals c,tables c] ++
    (functions c).map (fun i => Audited.pure (functionEntry c i)) ++
    (tags c).map (fun i => Audited.pure (tagEntry c i))

/-- Every branch constructs an import descriptor and its exact next context.
Unavailable function/tag kinds are omitted using prior-table metadata alone. -/
def generate (c : context) : Audited (Entry c) := (memories c).merge (alternatives c)

theorem memory_covers (c : context) (mt : memtype) (hm : MemtypeValidation.memtypeValid mt = true) :
    Gen.support (memories c).generator (memoryEntry c ⟨mt,hm⟩) := by
  refine ⟨⟨mt,hm⟩,?_,rfl⟩
  rw [ConstructiveAttach.refine_support,ConstructiveLimits.memories_support]
  exact hm
theorem global_covers (c : context) (gt : globaltype) (hg : GlobaltypeValidation.globaltypeValid c gt = true) :
    Gen.support (globals c).generator (globalEntry c ⟨gt,hg⟩) := by
  refine ⟨⟨gt,hg⟩,?_,rfl⟩
  rw [ConstructiveAttach.refine_support,globals_support]
  exact hg
theorem table_covers (c : context) (tt : tabletype) (ht : TabletypeValidation.tabletypeValid c tt = true) :
    Gen.support (tables c).generator (tableEntry c ⟨tt,ht⟩) := by
  refine ⟨⟨tt,ht⟩,?_,rfl⟩
  rw [ConstructiveAttach.refine_support,tables_support]
  exact ht

theorem branch_covers (c : context) (g : Audited (Entry c))
    (hg : g ∈ memories c :: alternatives c) (e : Entry c) (he : Gen.support g.generator e) :
    Gen.support (generate c).generator e :=
  (merge_support _ _ _).2 ⟨g,hg,he⟩

theorem complete (c out : context) (i : SpecTec.«import»)
    (h : ImportValidation.importDeclResult c i = some out) :
    ∃ e : Entry c, Gen.support (generate c).generator e ∧ e.descriptor = i.IDESC ∧ e.output = out := by
  rcases i with ⟨modName,itemName,desc⟩
  cases desc with
  | MemImport mt =>
    cases hv : MemtypeValidation.memtypeValid mt with
    | false => simp [ImportValidation.importDeclResult,hv] at h
    | true =>
      have hout : {c with MEMS := c.MEMS ++ [mt]} = out := by simpa [ImportValidation.importDeclResult,hv] using h
      exact ⟨memoryEntry c ⟨mt,hv⟩,branch_covers c (memories c) (by simp) _ (memory_covers c mt hv),rfl,hout⟩
  | GlobalImport gt =>
    cases hv : GlobaltypeValidation.globaltypeValid c gt with
    | false => simp [ImportValidation.importDeclResult,hv] at h
    | true =>
      have hout : {c with GLOBALS := c.GLOBALS ++ [gt]} = out := by simpa [ImportValidation.importDeclResult,hv] using h
      exact ⟨globalEntry c ⟨gt,hv⟩,branch_covers c (globals c) (by simp [alternatives]) _ (global_covers c gt hv),rfl,hout⟩
  | TableImport tt =>
    cases hv : TabletypeValidation.tabletypeValid c tt with
    | false => simp [ImportValidation.importDeclResult,hv] at h
    | true =>
      have hout : {c with TABLES := c.TABLES ++ [tt]} = out := by simpa [ImportValidation.importDeclResult,hv] using h
      exact ⟨tableEntry c ⟨tt,hv⟩,branch_covers c (tables c) (by simp [alternatives]) _ (table_covers c tt hv),rfl,hout⟩
  | FuncImport x =>
    cases hx : c.TYPES[x]? with
    | none => simp [ImportValidation.importDeclResult,ImportValidation.funcImportResult,hx] at h
    | some dt =>
      have hi := (List.getElem?_eq_some_iff.mp hx).1
      have hd : c.TYPES[x] = dt := (List.getElem?_eq_some_iff.mp hx).2
      cases hf : (UnrollInterface.deftypeFunctype dt).isSome with
      | false => simp [ImportValidation.importDeclResult,ImportValidation.funcImportResult,hx,hf] at h
      | true =>
        let index : FunctionIndex c := ⟨⟨x,hi⟩,by simpa [hd] using hf⟩
        have hm : index ∈ functions c := indices_cover c _ index.val index.property
        have hout : (functionEntry c index).output = out := by
          simpa [ImportValidation.importDeclResult,ImportValidation.funcImportResult,hx,hf,functionEntry,index,hd] using h
        refine ⟨functionEntry c index,branch_covers c (Audited.pure (functionEntry c index)) ?_ _ rfl,rfl,hout⟩
        simp only [alternatives,List.mem_cons,List.mem_append,List.mem_map]
        exact Or.inr (Or.inl (Or.inr ⟨index,hm,rfl⟩))
  | TagImport x =>
    cases hx : c.TYPES[x]? with
    | none => simp [ImportValidation.importDeclResult,ImportValidation.tagImportResult,hx] at h
    | some dt =>
      have hi := (List.getElem?_eq_some_iff.mp hx).1
      have hd : c.TYPES[x] = dt := (List.getElem?_eq_some_iff.mp hx).2
      cases hf : TagtypeValidation.tagtypeValid (.TagT dt) with
      | false => simp [ImportValidation.importDeclResult,ImportValidation.tagImportResult,hx,hf] at h
      | true =>
        let index : TagIndex c := ⟨⟨x,hi⟩,by simpa [hd] using hf⟩
        have hm : index ∈ tags c := indices_cover c _ index.val index.property
        have hout : (tagEntry c index).output = out := by
          simpa [ImportValidation.importDeclResult,ImportValidation.tagImportResult,hx,hf,tagEntry,index,hd] using h
        refine ⟨tagEntry c index,branch_covers c (Audited.pure (tagEntry c index)) ?_ _ rfl,rfl,hout⟩
        simp only [alternatives,List.mem_cons,List.mem_append,List.mem_map]
        exact Or.inr (Or.inr ⟨index,hm,rfl⟩)

end properties.wasm_module_ok.ConstructiveImportEntries
