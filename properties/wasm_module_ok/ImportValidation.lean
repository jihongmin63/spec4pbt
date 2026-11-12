import properties.wasm_module_ok.FunctionTypeValidation
import properties.wasm_module_ok.GlobaltypeValidation
import properties.wasm_module_ok.TabletypeValidation
import properties.wasm_module_ok.MemtypeValidation
import properties.wasm_module_ok.TagtypeValidation
import properties.wasm_module_ok.TagsValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ImportValidation

theorem global_clause_total (c : SpecTec.context)
    (i : SpecTec.«import») (gt : SpecTec.globaltype) (n : Nat)
    (hdesc : i.IDESC = .GlobalImport gt) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Import_ok:clause:1» c i)
      n (if GlobaltypeValidation.globaltypeValid c gt then
        .success (.of { c with GLOBALS := c.GLOBALS ++ [gt] })
        else .unmatch) n := by
  cases hv : GlobaltypeValidation.globaltypeValid c gt with
  | true =>
    unfold SpecTec.«Import_ok:clause:1»
    rw [hdesc]
    simp only [hv, ite_true]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
      · simpa [GlobaltypeValidation.globaltypeOutcome, hv] using
          GlobaltypeValidation.globaltype_total c gt n
      · exact SpecTecExecution.Eval.pure
          { c with GLOBALS := c.GLOBALS ++ [gt] }
  | false =>
    unfold SpecTec.«Import_ok:clause:1»
    rw [hdesc]
    simp only [hv, ite_false]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_unmatch
      simpa [GlobaltypeValidation.globaltypeOutcome, hv] using
        GlobaltypeValidation.globaltype_total c gt n

theorem table_clause_total (c : SpecTec.context)
    (i : SpecTec.«import») (tt : SpecTec.tabletype) (n : Nat)
    (hdesc : i.IDESC = .TableImport tt) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Import_ok:clause:2» c i)
      n (if TabletypeValidation.tabletypeValid c tt then
        .success (.of { c with TABLES := c.TABLES ++ [tt] })
        else .unmatch) n := by
  cases hv : TabletypeValidation.tabletypeValid c tt with
  | true =>
    unfold SpecTec.«Import_ok:clause:2»
    rw [hdesc]
    simp only [hv, ite_true]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
      · simpa [TabletypeValidation.tabletypeOutcome, hv] using
          TabletypeValidation.tabletype_total c tt n
      · exact SpecTecExecution.Eval.pure
          { c with TABLES := c.TABLES ++ [tt] }
  | false =>
    unfold SpecTec.«Import_ok:clause:2»
    rw [hdesc]
    simp only [hv, ite_false]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_unmatch
      simpa [TabletypeValidation.tabletypeOutcome, hv] using
        TabletypeValidation.tabletype_total c tt n

theorem mem_clause_total (c : SpecTec.context)
    (i : SpecTec.«import») (mt : SpecTec.memtype) (n : Nat)
    (hdesc : i.IDESC = .MemImport mt) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Import_ok:clause:3» c i)
      n (if MemtypeValidation.memtypeValid mt then
        .success (.of { c with MEMS := c.MEMS ++ [mt] })
        else .unmatch) n := by
  cases hv : MemtypeValidation.memtypeValid mt with
  | true =>
    unfold SpecTec.«Import_ok:clause:3»
    rw [hdesc]
    simp only [hv, ite_true]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_success
      · simpa [MemtypeValidation.memtypeOutcome, hv] using
          MemtypeValidation.memtype_total c mt n
      · exact SpecTecExecution.Eval.pure
          { c with MEMS := c.MEMS ++ [mt] }
  | false =>
    unfold SpecTec.«Import_ok:clause:3»
    rw [hdesc]
    simp only [hv, ite_false]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_unmatch
      simpa [MemtypeValidation.memtypeOutcome, hv] using
        MemtypeValidation.memtype_total c mt n

def funcImportResult (c : SpecTec.context) (x : SpecTec.typeidx) :
    Option SpecTec.context :=
  match c.TYPES[x]? with
  | none => none
  | some dt =>
      if (UnrollInterface.deftypeFunctype dt).isSome then
        some { c with FUNCS := c.FUNCS ++ [dt] }
      else none

def funcImportOutcome (c : SpecTec.context) (x : SpecTec.typeidx) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match funcImportResult c x with
  | none => .unmatch
  | some result => .success (.of result)

theorem func_clause_total (c : SpecTec.context)
    (i : SpecTec.«import») (x : SpecTec.typeidx) (n : Nat)
    (hdesc : i.IDESC = .FuncImport x) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Import_ok:clause:0» c i)
      n (funcImportOutcome c x) n := by
  cases hget : c.TYPES[x]? with
  | none =>
    unfold SpecTec.«Import_ok:clause:0»
    rw [hdesc]
    simp only [funcImportOutcome, funcImportResult, hget]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_unmatch
      have hf : FunctionTypeValidation.funcTypeResult c x = none := by
        simp [FunctionTypeValidation.funcTypeResult, hget]
      exact FunctionTypeValidation.func_type_none c x n hf
  | some dt =>
    cases hft : UnrollInterface.deftypeFunctype dt with
    | none =>
      unfold SpecTec.«Import_ok:clause:0»
      rw [hdesc]
      simp only [funcImportOutcome, funcImportResult, hget, hft,
        Option.isSome_none, ite_false]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_unmatch
        have hf : FunctionTypeValidation.funcTypeResult c x = none := by
          simp [FunctionTypeValidation.funcTypeResult, hget, hft]
        exact FunctionTypeValidation.func_type_none c x n hf
    | some ft =>
      have hbound : x < c.TYPES.length :=
        (List.getElem?_eq_some_iff.mp hget).1
      unfold SpecTec.«Import_ok:clause:0»
      rw [hdesc]
      simp only [funcImportOutcome, funcImportResult, hget, hft,
        Option.isSome_some, ite_true]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact (FunctionTypeValidation.func_type_success_iff_result
            c x ft n n).2
            ⟨by simp [FunctionTypeValidation.funcTypeResult, hget, hft], rfl⟩
        · apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true hbound
          · exact SpecTecExecution.Eval.pure
              { c with FUNCS := c.FUNCS ++ [dt] }

def tagImportResult (c : SpecTec.context) (x : SpecTec.typeidx) :
    Option SpecTec.context :=
  match c.TYPES[x]? with
  | none => none
  | some dt =>
      if TagtypeValidation.tagtypeValid (.TagT dt) then
        some { c with TAGS := c.TAGS ++ [SpecTec.tagtype.TagT dt] }
      else none

def tagImportOutcome (c : SpecTec.context) (x : SpecTec.typeidx) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match tagImportResult c x with
  | none => .unmatch
  | some result => .success (.of result)

theorem tag_clause_total (c : SpecTec.context)
    (i : SpecTec.«import») (x : SpecTec.typeidx) (n : Nat)
    (hdesc : i.IDESC = .TagImport x) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Import_ok:clause:4» c i)
      n (tagImportOutcome c x) n := by
  cases hget : c.TYPES[x]? with
  | none =>
    unfold SpecTec.«Import_ok:clause:4»
    rw [hdesc]
    simp only [tagImportOutcome, tagImportResult, hget]
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    · apply SpecTecExecution.Eval.bind_unmatch
      apply SpecTecExecution.Eval.guard_false
      have hnot : ¬ x < c.TYPES.length := by
        simpa using (List.getElem?_eq_none_iff.mp hget)
      exact hnot
  | some dt =>
    have hbound : x < c.TYPES.length :=
      (List.getElem?_eq_some_iff.mp hget).1
    cases hv : TagtypeValidation.tagtypeValid (.TagT dt) with
    | false =>
      unfold SpecTec.«Import_ok:clause:4»
      rw [hdesc]
      simp [tagImportOutcome, tagImportResult, hget, hv]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hbound
        · apply SpecTecExecution.Eval.bind_unmatch
          simpa [TagtypeValidation.tagtypeOutcome, hv] using
            TagtypeValidation.tagtype_total c (.TagT dt) n
    | true =>
      unfold SpecTec.«Import_ok:clause:4»
      rw [hdesc]
      simp [tagImportOutcome, tagImportResult, hget, hv]
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true rfl
      · apply SpecTecExecution.Eval.bind_success
        · exact SpecTecExecution.Eval.guard_true hbound
        · apply SpecTecExecution.Eval.bind_success
          · simpa [TagtypeValidation.tagtypeOutcome, hv] using
              TagtypeValidation.tagtype_total c (.TagT dt) n
          · exact SpecTecExecution.Eval.pure
              { c with TAGS := c.TAGS ++ [SpecTec.tagtype.TagT dt] }

def importDeclResult (c : SpecTec.context)
    (i : SpecTec.«import») : Option SpecTec.context :=
  match i.IDESC with
  | .FuncImport x => funcImportResult c x
  | .GlobalImport gt =>
      if GlobaltypeValidation.globaltypeValid c gt then
        some { c with GLOBALS := c.GLOBALS ++ [gt] } else none
  | .TableImport tt =>
      if TabletypeValidation.tabletypeValid c tt then
        some { c with TABLES := c.TABLES ++ [tt] } else none
  | .MemImport mt =>
      if MemtypeValidation.memtypeValid mt then
        some { c with MEMS := c.MEMS ++ [mt] } else none
  | .TagImport x => tagImportResult c x

def importDeclOutcome (c : SpecTec.context)
    (i : SpecTec.«import») :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match importDeclResult c i with
  | none => .unmatch
  | some result => .success (.of result)

private theorem clause0_mismatch (c : SpecTec.context)
    (i : SpecTec.«import») (n : Nat)
    (h : SpecTec.«exec:match:importdesc:FuncImport» i.IDESC = false) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Import_ok:clause:0» c i) n .unmatch n := by
  unfold SpecTec.«Import_ok:clause:0»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  simp [h]

private theorem clause1_mismatch (c : SpecTec.context)
    (i : SpecTec.«import») (n : Nat)
    (h : SpecTec.«exec:match:importdesc:GlobalImport» i.IDESC = false) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Import_ok:clause:1» c i) n .unmatch n := by
  unfold SpecTec.«Import_ok:clause:1»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  simp [h]

private theorem clause2_mismatch (c : SpecTec.context)
    (i : SpecTec.«import») (n : Nat)
    (h : SpecTec.«exec:match:importdesc:TableImport» i.IDESC = false) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Import_ok:clause:2» c i) n .unmatch n := by
  unfold SpecTec.«Import_ok:clause:2»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  simp [h]

private theorem clause3_mismatch (c : SpecTec.context)
    (i : SpecTec.«import») (n : Nat)
    (h : SpecTec.«exec:match:importdesc:MemImport» i.IDESC = false) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Import_ok:clause:3» c i) n .unmatch n := by
  unfold SpecTec.«Import_ok:clause:3»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  simp [h]

private theorem clause4_mismatch (c : SpecTec.context)
    (i : SpecTec.«import») (n : Nat)
    (h : SpecTec.«exec:match:importdesc:TagImport» i.IDESC = false) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Import_ok:clause:4» c i) n .unmatch n := by
  unfold SpecTec.«Import_ok:clause:4»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  simp [h]

theorem import_func_total (c : SpecTec.context)
    (i : SpecTec.«import») (x : SpecTec.typeidx) (n : Nat)
    (hdesc : i.IDESC = .FuncImport x) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Import_ok c i⟩)
      n (funcImportOutcome c x) n := by
  cases hr : funcImportResult c x with
  | some result =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Import_ok_clauses c i))
      n (funcImportOutcome c x) n
    simp only [funcImportOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_success
    exact (by simpa [funcImportOutcome, hr] using
      func_clause_total c i x n hdesc)
  | none =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Import_ok_clauses c i))
      n (funcImportOutcome c x) n
    simp only [funcImportOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · simpa [funcImportOutcome, hr] using
        func_clause_total c i x n hdesc
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c i n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c i n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · exact clause3_mismatch c i n (by rw [hdesc]; rfl)
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · exact clause4_mismatch c i n (by rw [hdesc]; rfl)
            · exact SpecTecExecution.tryClauses_nil n

theorem import_global_total (c : SpecTec.context)
    (i : SpecTec.«import») (gt : SpecTec.globaltype) (n : Nat)
    (hdesc : i.IDESC = .GlobalImport gt) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Import_ok c i⟩)
      n (if GlobaltypeValidation.globaltypeValid c gt then
        .success (.of { c with GLOBALS := c.GLOBALS ++ [gt] })
        else .unmatch) n := by
  cases hv : GlobaltypeValidation.globaltypeValid c gt with
  | true =>
    simp only [hv, ite_true]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Import_ok_clauses c i))
      n (.success (.of { c with GLOBALS := c.GLOBALS ++ [gt] })) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c i n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_success
      simpa [hv] using global_clause_total c i gt n hdesc
  | false =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Import_ok_clauses c i))
      n .unmatch n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c i n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · simpa [hv] using global_clause_total c i gt n hdesc
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c i n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · exact clause3_mismatch c i n (by rw [hdesc]; rfl)
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · exact clause4_mismatch c i n (by rw [hdesc]; rfl)
            · exact SpecTecExecution.tryClauses_nil n

theorem import_table_total (c : SpecTec.context)
    (i : SpecTec.«import») (tt : SpecTec.tabletype) (n : Nat)
    (hdesc : i.IDESC = .TableImport tt) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Import_ok c i⟩)
      n (if TabletypeValidation.tabletypeValid c tt then
        .success (.of { c with TABLES := c.TABLES ++ [tt] })
        else .unmatch) n := by
  cases hv : TabletypeValidation.tabletypeValid c tt with
  | true =>
    simp only [hv, ite_true]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Import_ok_clauses c i))
      n (.success (.of { c with TABLES := c.TABLES ++ [tt] })) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c i n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c i n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_success
        simpa [hv] using table_clause_total c i tt n hdesc
  | false =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Import_ok_clauses c i))
      n .unmatch n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c i n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c i n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · simpa [hv] using table_clause_total c i tt n hdesc
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · exact clause3_mismatch c i n (by rw [hdesc]; rfl)
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · exact clause4_mismatch c i n (by rw [hdesc]; rfl)
            · exact SpecTecExecution.tryClauses_nil n

theorem import_mem_total (c : SpecTec.context)
    (i : SpecTec.«import») (mt : SpecTec.memtype) (n : Nat)
    (hdesc : i.IDESC = .MemImport mt) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Import_ok c i⟩)
      n (if MemtypeValidation.memtypeValid mt then
        .success (.of { c with MEMS := c.MEMS ++ [mt] })
        else .unmatch) n := by
  cases hv : MemtypeValidation.memtypeValid mt with
  | true =>
    simp only [hv, ite_true]
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Import_ok_clauses c i))
      n (.success (.of { c with MEMS := c.MEMS ++ [mt] })) n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c i n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c i n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c i n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_success
          simpa [hv] using mem_clause_total c i mt n hdesc
  | false =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Import_ok_clauses c i))
      n .unmatch n
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c i n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c i n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c i n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · simpa [hv] using mem_clause_total c i mt n hdesc
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · exact clause4_mismatch c i n (by rw [hdesc]; rfl)
            · exact SpecTecExecution.tryClauses_nil n

theorem import_tag_total (c : SpecTec.context)
    (i : SpecTec.«import») (x : SpecTec.typeidx) (n : Nat)
    (hdesc : i.IDESC = .TagImport x) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Import_ok c i⟩)
      n (tagImportOutcome c x) n := by
  cases hr : tagImportResult c x with
  | some result =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Import_ok_clauses c i))
      n (tagImportOutcome c x) n
    simp only [tagImportOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c i n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c i n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c i n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · exact clause3_mismatch c i n (by rw [hdesc]; rfl)
          · apply SpecTecExecution.tryClauses_cons_success
            simpa [tagImportOutcome, hr] using
              tag_clause_total c i x n hdesc
  | none =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Import_ok_clauses c i))
      n (tagImportOutcome c x) n
    simp only [tagImportOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c i n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c i n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c i n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · exact clause3_mismatch c i n (by rw [hdesc]; rfl)
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · simpa [tagImportOutcome, hr] using
                tag_clause_total c i x n hdesc
            · exact SpecTecExecution.tryClauses_nil n

theorem import_ok_total (c : SpecTec.context)
    (i : SpecTec.«import») (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Import_ok c i⟩)
      n (importDeclOutcome c i) n := by
  cases hdesc : i.IDESC with
  | FuncImport x =>
    simpa [importDeclOutcome, importDeclResult, hdesc,
      funcImportOutcome] using import_func_total c i x n hdesc
  | GlobalImport gt =>
    cases hv : GlobaltypeValidation.globaltypeValid c gt <;>
      simpa [importDeclOutcome, importDeclResult, hdesc, hv] using
        import_global_total c i gt n hdesc
  | TableImport tt =>
    cases hv : TabletypeValidation.tabletypeValid c tt <;>
      simpa [importDeclOutcome, importDeclResult, hdesc, hv] using
        import_table_total c i tt n hdesc
  | MemImport mt =>
    cases hv : MemtypeValidation.memtypeValid mt <;>
      simpa [importDeclOutcome, importDeclResult, hdesc, hv] using
        import_mem_total c i mt n hdesc
  | TagImport x =>
    simpa [importDeclOutcome, importDeclResult, hdesc,
      tagImportOutcome] using import_tag_total c i x n hdesc

theorem import_ok_success_iff_result (c : SpecTec.context)
    (i : SpecTec.«import») (result : SpecTec.context)
    (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Import_ok c i⟩)
      n (.success (.of result)) finalSupply ↔
    importDeclResult c i = some result ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h (import_ok_total c i n)
    cases hr : importDeclResult c i with
    | none => simp [importDeclOutcome, hr] at hout
    | some result' =>
      simp [importDeclOutcome, hr] at hout
      cases hout
      exact ⟨rfl, hsupply⟩
  · rintro ⟨hr, rfl⟩
    simpa [importDeclOutcome, hr] using import_ok_total c i finalSupply

theorem import_ok_none (c : SpecTec.context)
    (i : SpecTec.«import») (n : Nat)
    (hr : importDeclResult c i = none) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.Import_ok c i⟩)
      n .unmatch n := by
  simpa [importDeclOutcome, hr] using import_ok_total c i n

end properties.wasm_module_ok.ImportValidation
