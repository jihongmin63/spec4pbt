import properties.wasm_module_ok.ExportSetValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ExportValidation

def namesetAdd (names : SpecTec.nameset) (name : SpecTec.name) :
    SpecTec.nameset :=
  @SpecTec.«$union_set» SpecTec.name
    ({ key := fun values => .node 8
        (values.map (fun value =>
          (@_root_.SpecTecCompareKey.key Nat (inferInstance) value))) }
      : _root_.SpecTecCompareKey (List Nat))
    names (SpecTec.set.«`{ % `}» [name])

def exportTail (bound x : Nat) (name : SpecTec.name)
    (names : SpecTec.nameset) :
    SpecTecExecution.Action.{1} SpecTec.Request :=
  (SpecTecExecution.Action.guard (x ≥ 0 ∧ x < bound)).bind fun (_ : Unit) =>
  (SpecTecExecution.Action.call ⟨Bool,
    SpecTec.Call.«$in_set» SpecTec.name name names⟩).bind fun (used : Bool) =>
  (SpecTecExecution.Action.guard (¬ (used = true))).bind fun (_ : Unit) =>
  SpecTecExecution.Action.pure (namesetAdd names name)

def exportTailResult (bound x : Nat) (name : SpecTec.name)
    (names : SpecTec.nameset) : Option SpecTec.nameset :=
  if x < bound && !ExportSetValidation.inSetResult name names then
    some (namesetAdd names name)
  else none

def exportTailOutcome (bound x : Nat) (name : SpecTec.name)
    (names : SpecTec.nameset) :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match exportTailResult bound x name names with
  | none => .unmatch
  | some result => .success (.of result)

theorem export_tail_total (bound x : Nat) (name : SpecTec.name)
    (names : SpecTec.nameset) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (exportTail bound x name names)
      n (exportTailOutcome bound x name names) n := by
  by_cases hb : x < bound
  · cases hu : ExportSetValidation.inSetResult name names with
    | false =>
      simp [exportTailOutcome, exportTailResult, hb, hu]
      unfold exportTail
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true ⟨Nat.zero_le x, hb⟩
      · apply SpecTecExecution.Eval.bind_success
        · exact ExportSetValidation.in_set_total name names n
        · apply SpecTecExecution.Eval.bind_success
          · exact SpecTecExecution.Eval.guard_true (by simp [hu])
          · exact SpecTecExecution.Eval.pure (namesetAdd names name)
    | true =>
      simp [exportTailOutcome, exportTailResult, hb, hu]
      unfold exportTail
      apply SpecTecExecution.Eval.bind_success
      · exact SpecTecExecution.Eval.guard_true ⟨Nat.zero_le x, hb⟩
      · apply SpecTecExecution.Eval.bind_success
        · exact ExportSetValidation.in_set_total name names n
        · apply SpecTecExecution.Eval.bind_unmatch
          apply SpecTecExecution.Eval.guard_false
          simp [hu]
  · simp [exportTailOutcome, exportTailResult, hb]
    unfold exportTail
    apply SpecTecExecution.Eval.bind_unmatch
    apply SpecTecExecution.Eval.guard_false
    intro h
    exact hb h.2

theorem export_func_clause_total (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export»)
    (x n : Nat) (hdesc : e.EDESC = .FuncExport x) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Export_ok:clause:0» c names e)
      n (exportTailOutcome c.FUNCS.length x e.NAME names) n := by
  unfold SpecTec.«Export_ok:clause:0»
  rw [hdesc]
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · change SpecTecExecution.Eval SpecTec.Body
      (exportTail c.FUNCS.length x e.NAME names)
      n (exportTailOutcome c.FUNCS.length x e.NAME names) n
    exact export_tail_total c.FUNCS.length x e.NAME names n

theorem export_global_clause_total (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export»)
    (x n : Nat) (hdesc : e.EDESC = .GlobalExport x) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Export_ok:clause:1» c names e)
      n (exportTailOutcome c.GLOBALS.length x e.NAME names) n := by
  unfold SpecTec.«Export_ok:clause:1»
  rw [hdesc]
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · change SpecTecExecution.Eval SpecTec.Body
      (exportTail c.GLOBALS.length x e.NAME names)
      n (exportTailOutcome c.GLOBALS.length x e.NAME names) n
    exact export_tail_total c.GLOBALS.length x e.NAME names n

theorem export_table_clause_total (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export»)
    (x n : Nat) (hdesc : e.EDESC = .TableExport x) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Export_ok:clause:2» c names e)
      n (exportTailOutcome c.TABLES.length x e.NAME names) n := by
  unfold SpecTec.«Export_ok:clause:2»
  rw [hdesc]
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · change SpecTecExecution.Eval SpecTec.Body
      (exportTail c.TABLES.length x e.NAME names)
      n (exportTailOutcome c.TABLES.length x e.NAME names) n
    exact export_tail_total c.TABLES.length x e.NAME names n

theorem export_mem_clause_total (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export»)
    (x n : Nat) (hdesc : e.EDESC = .MemExport x) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Export_ok:clause:3» c names e)
      n (exportTailOutcome c.MEMS.length x e.NAME names) n := by
  unfold SpecTec.«Export_ok:clause:3»
  rw [hdesc]
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · change SpecTecExecution.Eval SpecTec.Body
      (exportTail c.MEMS.length x e.NAME names)
      n (exportTailOutcome c.MEMS.length x e.NAME names) n
    exact export_tail_total c.MEMS.length x e.NAME names n

theorem export_tag_clause_total (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export»)
    (x n : Nat) (hdesc : e.EDESC = .TagExport x) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Export_ok:clause:4» c names e)
      n (exportTailOutcome c.TAGS.length x e.NAME names) n := by
  unfold SpecTec.«Export_ok:clause:4»
  rw [hdesc]
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  · change SpecTecExecution.Eval SpecTec.Body
      (exportTail c.TAGS.length x e.NAME names)
      n (exportTailOutcome c.TAGS.length x e.NAME names) n
    exact export_tail_total c.TAGS.length x e.NAME names n

def exportResult (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export») :
    Option SpecTec.nameset :=
  match e.EDESC with
  | .FuncExport x => exportTailResult c.FUNCS.length x e.NAME names
  | .GlobalExport x => exportTailResult c.GLOBALS.length x e.NAME names
  | .TableExport x => exportTailResult c.TABLES.length x e.NAME names
  | .MemExport x => exportTailResult c.MEMS.length x e.NAME names
  | .TagExport x => exportTailResult c.TAGS.length x e.NAME names

def exportOutcome (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export») :
    SpecTecExecution.Outcome SpecTecExecution.Value :=
  match exportResult c names e with
  | none => .unmatch
  | some result => .success (.of result)

private theorem clause0_mismatch (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export») (n : Nat)
    (h : SpecTec.«exec:match:exportdesc:FuncExport» e.EDESC = false) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Export_ok:clause:0» c names e) n .unmatch n := by
  unfold SpecTec.«Export_ok:clause:0»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  simp [h]

private theorem clause1_mismatch (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export») (n : Nat)
    (h : SpecTec.«exec:match:exportdesc:GlobalExport» e.EDESC = false) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Export_ok:clause:1» c names e) n .unmatch n := by
  unfold SpecTec.«Export_ok:clause:1»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  simp [h]

private theorem clause2_mismatch (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export») (n : Nat)
    (h : SpecTec.«exec:match:exportdesc:TableExport» e.EDESC = false) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Export_ok:clause:2» c names e) n .unmatch n := by
  unfold SpecTec.«Export_ok:clause:2»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  simp [h]

private theorem clause3_mismatch (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export») (n : Nat)
    (h : SpecTec.«exec:match:exportdesc:MemExport» e.EDESC = false) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Export_ok:clause:3» c names e) n .unmatch n := by
  unfold SpecTec.«Export_ok:clause:3»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  simp [h]

private theorem clause4_mismatch (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export») (n : Nat)
    (h : SpecTec.«exec:match:exportdesc:TagExport» e.EDESC = false) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«Export_ok:clause:4» c names e) n .unmatch n := by
  unfold SpecTec.«Export_ok:clause:4»
  apply SpecTecExecution.Eval.bind_unmatch
  apply SpecTecExecution.Eval.guard_false
  simp [h]

theorem export_func_total (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export»)
    (x n : Nat) (hdesc : e.EDESC = .FuncExport x) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.nameset,
        SpecTec.Call.Export_ok c names e⟩)
      n (exportTailOutcome c.FUNCS.length x e.NAME names) n := by
  cases hr : exportTailResult c.FUNCS.length x e.NAME names with
  | some result =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Export_ok_clauses c names e))
      n (exportTailOutcome c.FUNCS.length x e.NAME names) n
    simp only [exportTailOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_success
    simpa [exportTailOutcome, hr] using
      export_func_clause_total c names e x n hdesc
  | none =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Export_ok_clauses c names e))
      n (exportTailOutcome c.FUNCS.length x e.NAME names) n
    simp only [exportTailOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · simpa [exportTailOutcome, hr] using
        export_func_clause_total c names e x n hdesc
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c names e n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c names e n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · exact clause3_mismatch c names e n (by rw [hdesc]; rfl)
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · exact clause4_mismatch c names e n (by rw [hdesc]; rfl)
            · exact SpecTecExecution.tryClauses_nil n


theorem export_global_total (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export»)
    (x n : Nat) (hdesc : e.EDESC = .GlobalExport x) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.nameset,
        SpecTec.Call.Export_ok c names e⟩)
      n (exportTailOutcome c.GLOBALS.length x e.NAME names) n := by
  cases hr : exportTailResult c.GLOBALS.length x e.NAME names with
  | some result =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Export_ok_clauses c names e))
      n (exportTailOutcome c.GLOBALS.length x e.NAME names) n
    simp only [exportTailOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c names e n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_success
      simpa [exportTailOutcome, hr] using
        export_global_clause_total c names e x n hdesc
  | none =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Export_ok_clauses c names e))
      n (exportTailOutcome c.GLOBALS.length x e.NAME names) n
    simp only [exportTailOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c names e n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · simpa [exportTailOutcome, hr] using
          export_global_clause_total c names e x n hdesc
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c names e n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · exact clause3_mismatch c names e n (by rw [hdesc]; rfl)
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · exact clause4_mismatch c names e n (by rw [hdesc]; rfl)
            · exact SpecTecExecution.tryClauses_nil n

theorem export_table_total (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export»)
    (x n : Nat) (hdesc : e.EDESC = .TableExport x) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.nameset,
        SpecTec.Call.Export_ok c names e⟩)
      n (exportTailOutcome c.TABLES.length x e.NAME names) n := by
  cases hr : exportTailResult c.TABLES.length x e.NAME names with
  | some result =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Export_ok_clauses c names e))
      n (exportTailOutcome c.TABLES.length x e.NAME names) n
    simp only [exportTailOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c names e n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c names e n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_success
        simpa [exportTailOutcome, hr] using
          export_table_clause_total c names e x n hdesc
  | none =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Export_ok_clauses c names e))
      n (exportTailOutcome c.TABLES.length x e.NAME names) n
    simp only [exportTailOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c names e n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c names e n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · simpa [exportTailOutcome, hr] using
            export_table_clause_total c names e x n hdesc
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · exact clause3_mismatch c names e n (by rw [hdesc]; rfl)
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · exact clause4_mismatch c names e n (by rw [hdesc]; rfl)
            · exact SpecTecExecution.tryClauses_nil n

theorem export_mem_total (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export»)
    (x n : Nat) (hdesc : e.EDESC = .MemExport x) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.nameset,
        SpecTec.Call.Export_ok c names e⟩)
      n (exportTailOutcome c.MEMS.length x e.NAME names) n := by
  cases hr : exportTailResult c.MEMS.length x e.NAME names with
  | some result =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Export_ok_clauses c names e))
      n (exportTailOutcome c.MEMS.length x e.NAME names) n
    simp only [exportTailOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c names e n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c names e n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c names e n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_success
          simpa [exportTailOutcome, hr] using
            export_mem_clause_total c names e x n hdesc
  | none =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Export_ok_clauses c names e))
      n (exportTailOutcome c.MEMS.length x e.NAME names) n
    simp only [exportTailOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c names e n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c names e n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c names e n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · simpa [exportTailOutcome, hr] using
              export_mem_clause_total c names e x n hdesc
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · exact clause4_mismatch c names e n (by rw [hdesc]; rfl)
            · exact SpecTecExecution.tryClauses_nil n

theorem export_tag_total (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export»)
    (x n : Nat) (hdesc : e.EDESC = .TagExport x) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.nameset,
        SpecTec.Call.Export_ok c names e⟩)
      n (exportTailOutcome c.TAGS.length x e.NAME names) n := by
  cases hr : exportTailResult c.TAGS.length x e.NAME names with
  | some result =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Export_ok_clauses c names e))
      n (exportTailOutcome c.TAGS.length x e.NAME names) n
    simp only [exportTailOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c names e n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c names e n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c names e n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · exact clause3_mismatch c names e n (by rw [hdesc]; rfl)
          · apply SpecTecExecution.tryClauses_cons_success
            simpa [exportTailOutcome, hr] using
              export_tag_clause_total c names e x n hdesc
  | none =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses
        (SpecTec.Export_ok_clauses c names e))
      n (exportTailOutcome c.TAGS.length x e.NAME names) n
    simp only [exportTailOutcome, hr]
    apply SpecTecExecution.tryClauses_cons_unmatch
    · exact clause0_mismatch c names e n (by rw [hdesc]; rfl)
    · apply SpecTecExecution.tryClauses_cons_unmatch
      · exact clause1_mismatch c names e n (by rw [hdesc]; rfl)
      · apply SpecTecExecution.tryClauses_cons_unmatch
        · exact clause2_mismatch c names e n (by rw [hdesc]; rfl)
        · apply SpecTecExecution.tryClauses_cons_unmatch
          · exact clause3_mismatch c names e n (by rw [hdesc]; rfl)
          · apply SpecTecExecution.tryClauses_cons_unmatch
            · simpa [exportTailOutcome, hr] using
                export_tag_clause_total c names e x n hdesc
            · exact SpecTecExecution.tryClauses_nil n

theorem export_ok_total (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export») (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.nameset,
        SpecTec.Call.Export_ok c names e⟩)
      n (exportOutcome c names e) n := by
  cases hdesc : e.EDESC with
  | FuncExport x =>
    simpa [exportOutcome, exportResult, hdesc, exportTailOutcome] using
      export_func_total c names e x n hdesc
  | GlobalExport x =>
    simpa [exportOutcome, exportResult, hdesc, exportTailOutcome] using
      export_global_total c names e x n hdesc
  | TableExport x =>
    simpa [exportOutcome, exportResult, hdesc, exportTailOutcome] using
      export_table_total c names e x n hdesc
  | MemExport x =>
    simpa [exportOutcome, exportResult, hdesc, exportTailOutcome] using
      export_mem_total c names e x n hdesc
  | TagExport x =>
    simpa [exportOutcome, exportResult, hdesc, exportTailOutcome] using
      export_tag_total c names e x n hdesc

theorem export_ok_success_iff_result (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export»)
    (result : SpecTec.nameset) (n finalSupply : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.nameset,
        SpecTec.Call.Export_ok c names e⟩)
      n (.success (.of result)) finalSupply ↔
    exportResult c names e = some result ∧ finalSupply = n := by
  constructor
  · intro h
    obtain ⟨hout, hsupply⟩ :=
      properties.wasm_module_ok.Execution.eval_deterministic h
        (export_ok_total c names e n)
    cases hr : exportResult c names e with
    | none => simp [exportOutcome, hr] at hout
    | some result' =>
      simp [exportOutcome, hr] at hout
      cases hout
      exact ⟨rfl, hsupply⟩
  · rintro ⟨hr, rfl⟩
    simpa [exportOutcome, hr] using
      export_ok_total c names e finalSupply

theorem export_ok_none (c : SpecTec.context)
    (names : SpecTec.nameset) (e : SpecTec.«export») (n : Nat)
    (hr : exportResult c names e = none) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.nameset,
        SpecTec.Call.Export_ok c names e⟩)
      n .unmatch n := by
  simpa [exportOutcome, hr] using export_ok_total c names e n

end properties.wasm_module_ok.ExportValidation
