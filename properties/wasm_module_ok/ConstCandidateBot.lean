import properties.wasm_module_ok.ConstTargetShape
import properties.wasm_module_ok.GlobaltypeValidation
import properties.wasm_module_ok.ImportValidation
import properties.wasm_module_ok.ImportsValidation
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_ok.ConstCandidateBot

theorem bot_mem_candidate_iff
    (c : SpecTec.context) :
    SpecTec.valtype.BotT ∈
      FiniteValidTypes.candidateUniverse c ↔
    ∃ m : SpecTec.«mut»,
      SpecTec.globaltype.GlobalT m .BotT ∈ c.GLOBALS := by
  have hvalid : SpecTec.valtype.BotT ∉
      FiniteValidTypes.validCandidates c := by
    simp [FiniteValidTypes.validCandidates,
      FiniteValidTypes.refCandidates, List.mem_flatMap]
  have hinternal : SpecTec.valtype.BotT ∉
      FiniteValidTypes.internalRefCandidates
        (c.TYPES ++ c.FUNCS) := by
    simp [FiniteValidTypes.internalRefCandidates,
      List.mem_flatMap]
  simp only [FiniteValidTypes.candidateUniverse,
    List.mem_toFinset, FiniteValidTypes.candidateTypes,
    List.mem_append, hvalid, hinternal, false_or]
  constructor
  · intro h
    obtain ⟨gt, hgt, heq⟩ := List.mem_map.mp h
    cases gt with
    | GlobalT m t =>
        cases t with
        | BotT => exact ⟨m, hgt⟩
        | NumT _ => cases heq
        | VecT _ => cases heq
        | RefT _ => cases heq
  · rintro ⟨m, hgt⟩
    exact List.mem_map.mpr
      ⟨SpecTec.globaltype.GlobalT m .BotT, hgt, rfl⟩

theorem globaltype_success_not_bot
    (c : SpecTec.context) (m : SpecTec.«mut»)
    (t : SpecTec.valtype) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Globaltype_ok c (.GlobalT m t)⟩)
      start (.success (.of ())) fin) :
    t ≠ .BotT := by
  have hv :=
    (GlobaltypeValidation.globaltype_success_iff_valid
      c (.GlobalT m t) start fin).1 h
  intro hbot
  subst t
  simp [GlobaltypeValidation.globaltypeValid,
    ValtypeValidation.valtypeValid] at hv

theorem import_result_preserves_no_bot
    (c out : SpecTec.context) (i : SpecTec.«import»)
    (hinput : ∀ m, SpecTec.globaltype.GlobalT m .BotT ∉ c.GLOBALS)
    (hresult : ImportValidation.importDeclResult c i = some out) :
    ∀ m, SpecTec.globaltype.GlobalT m .BotT ∉ out.GLOBALS := by
  cases hdesc : i.IDESC with
  | FuncImport x =>
      simp only [ImportValidation.importDeclResult, hdesc,
        ImportValidation.funcImportResult] at hresult
      split at hresult <;> try contradiction
      split at hresult <;> try contradiction
      cases hresult
      simpa using hinput

  | GlobalImport gt =>
      cases gt with
      | GlobalT mutation t =>
          by_cases hv : GlobaltypeValidation.globaltypeValid c
              (.GlobalT mutation t) = true
          · simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
            cases hresult
            have hnot : t ≠ .BotT := by
              intro ht
              subst t
              simp [GlobaltypeValidation.globaltypeValid,
                ValtypeValidation.valtypeValid] at hv
            intro m hmem
            rcases List.mem_append.mp hmem with hold | hnew
            · exact hinput m hold
            · have heq := List.mem_singleton.mp hnew
              cases heq
              exact hnot rfl
          · simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
  | TableImport tt =>
      by_cases hv : TabletypeValidation.tabletypeValid c tt = true
      · simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
        cases hresult
        simpa using hinput
      · simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
  | MemImport mt =>
      by_cases hv : MemtypeValidation.memtypeValid mt = true
      · simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
        cases hresult
        simpa using hinput
      · simp [ImportValidation.importDeclResult, hdesc, hv] at hresult
  | TagImport x =>
      simp only [ImportValidation.importDeclResult, hdesc,
        ImportValidation.tagImportResult] at hresult
      split at hresult <;> try contradiction
      split at hresult <;> try contradiction
      cases hresult
      simpa using hinput

theorem global_success_preserves_no_bot
    (c out : SpecTec.context) (g : SpecTec.global)
    (start fin : Nat)
    (hinput : ∀ m, SpecTec.globaltype.GlobalT m .BotT ∉ c.GLOBALS)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Global_ok c g⟩)
      start (.success (.of out)) fin) :
    ∀ m, SpecTec.globaltype.GlobalT m .BotT ∉ out.GLOBALS := by
  cases h with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.Global_ok_clauses c g))
        start (.success (.of out)) fin at hbody
      cases hbody with
      | orElse_success hclause =>
          cases htype : g.GTYPE with
          | GlobalT mutation t =>
              unfold SpecTec.«Global_ok:clause:0» at hclause
              rw [htype] at hclause
              cases hclause with
              | bind_success hgt htail =>
                  cases htail with
                  | bind_success _ hpure =>
                      cases hpure with
                      | pure =>
                          have hnot := globaltype_success_not_bot
                            c mutation t start _ hgt
                          intro m hmem
                          rcases List.mem_append.mp hmem with
                            hold | hnew
                          · exact hinput m hold
                          · have heq := List.mem_singleton.mp hnew
                            cases heq
                            exact hnot rfl
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem globals_success_no_bot
    (c out : SpecTec.context) (gs : List SpecTec.global)
    (start fin : Nat)
    (hinput : ∀ m, SpecTec.globaltype.GlobalT m .BotT ∉ c.GLOBALS)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Globals_ok c gs⟩)
      start (.success (.of out)) fin) :
    ∀ m, SpecTec.globaltype.GlobalT m .BotT ∉ out.GLOBALS := by
  induction gs generalizing c start fin out with
  | nil =>
      cases h with
      | call hbody =>
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Globals_ok:clause:0» c [])
              (fun _ => SpecTecExecution.tryClauses
                [SpecTec.«Globals_ok:clause:1» c []]))
            start (.success (.of out)) fin at hbody
          cases hbody with
          | orElse_success hfirst =>
              unfold SpecTec.«Globals_ok:clause:0» at hfirst
              cases hfirst with
              | bind_success hguard _ =>
                  cases hguard with
                  | guard_true hcond => simp at hcond
          | orElse_unmatch hfailedSupply htail =>
              restore_supply hfailedSupply at htail
              change SpecTecExecution.Eval SpecTec.Body
                (.orElse (SpecTec.«Globals_ok:clause:1» c [])
                  (fun _ => .unmatch))
                start (.success (.of out)) fin at htail
              cases htail with
              | orElse_success hsecond =>
                  unfold SpecTec.«Globals_ok:clause:1» at hsecond
                  cases hsecond with
                  | bind_success _ hpure =>
                      cases hpure with
                      | pure => exact hinput
              | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone
  | cons g rest ih =>
      cases h with
      | call hbody =>
          change SpecTecExecution.Eval SpecTec.Body
            (.orElse (SpecTec.«Globals_ok:clause:0» c (g :: rest))
              (fun _ => SpecTecExecution.tryClauses
                [SpecTec.«Globals_ok:clause:1» c (g :: rest)]))
            start (.success (.of out)) fin at hbody
          cases hbody with
          | orElse_success hfirst =>
              unfold SpecTec.«Globals_ok:clause:0» at hfirst
              cases hfirst with
              | bind_success hguard htail =>
                  cases hguard with
                  | guard_true _ =>
                      cases htail with
                      | bind_success hhead htail =>
                          rename_i middle c₁
                          cases htail with
                          | bind_success hrest hpure =>
                              cases hpure with
                              | pure =>
                                  exact ih c₁ out middle fin
                                    (global_success_preserves_no_bot
                                      c c₁ g start middle hinput hhead)
                                    hrest
          | orElse_unmatch hfailedSupply htail =>
              restore_supply hfailedSupply at htail
              change SpecTecExecution.Eval SpecTec.Body
                (.orElse (SpecTec.«Globals_ok:clause:1» c (g :: rest))
                  (fun _ => .unmatch))
                start (.success (.of out)) fin at htail
              cases htail with
              | orElse_success hsecond =>
                  unfold SpecTec.«Globals_ok:clause:1» at hsecond
                  cases hsecond with
                  | bind_success hguard _ =>
                      cases hguard with
                      | guard_true hcond => simp at hcond
              | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem imports_result_preserves_no_bot
    (c out : SpecTec.context) (is : List SpecTec.«import»)
    (hinput : ∀ m, SpecTec.globaltype.GlobalT m .BotT ∉ c.GLOBALS)
    (hresult : ImportsValidation.importsResult c is = some out) :
    ∀ m, SpecTec.globaltype.GlobalT m .BotT ∉ out.GLOBALS := by
  induction is generalizing c with
  | nil =>
      simp only [ImportsValidation.importsResult] at hresult
      cases hresult
      exact hinput
  | cons i is ih =>
      simp only [ImportsValidation.importsResult] at hresult
      cases hhead : ImportValidation.importDeclResult c i with
      | none => simp [hhead] at hresult
      | some c₁ =>
          simp only [hhead, Option.bind_some] at hresult
          exact ih c₁
            (import_result_preserves_no_bot c c₁ i hinput hhead)
            hresult

theorem imports_success_no_bot
    (c out : SpecTec.context) (is : List SpecTec.«import»)
    (start fin : Nat)
    (hinput : ∀ m, SpecTec.globaltype.GlobalT m .BotT ∉ c.GLOBALS)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Imports_ok c is⟩)
      start (.success (.of out)) fin) :
    ∀ m, SpecTec.globaltype.GlobalT m .BotT ∉ out.GLOBALS := by
  exact imports_result_preserves_no_bot c out is hinput
    ((ImportsValidation.imports_success_iff_result
      c is out start fin).1 h).1

theorem imports_success_no_bot_candidate
    (c out : SpecTec.context) (is : List SpecTec.«import»)
    (start fin : Nat)
    (hinput : SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse c)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Imports_ok c is⟩)
      start (.success (.of out)) fin) :
    SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse out := by
  have hglobals : ∀ m,
      SpecTec.globaltype.GlobalT m .BotT ∉ c.GLOBALS := by
    intro m hm
    exact hinput ((bot_mem_candidate_iff c).2 ⟨m, hm⟩)
  have hout := imports_success_no_bot c out is start fin hglobals h
  intro hb
  obtain ⟨m, hm⟩ := (bot_mem_candidate_iff out).1 hb
  exact hout m hm

theorem globals_success_no_bot_candidate
    (c out : SpecTec.context) (gs : List SpecTec.global)
    (start fin : Nat)
    (hinput : SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse c)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Globals_ok c gs⟩)
      start (.success (.of out)) fin) :
    SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse out := by
  have hglobals : ∀ m,
      SpecTec.globaltype.GlobalT m .BotT ∉ c.GLOBALS := by
    intro m hm
    exact hinput ((bot_mem_candidate_iff c).2 ⟨m, hm⟩)
  have hout := globals_success_no_bot c out gs start fin hglobals h
  intro hb
  obtain ⟨m, hm⟩ := (bot_mem_candidate_iff out).1 hb
  exact hout m hm

theorem empty_context_globals_nil
    (out : SpecTec.context) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.«$empty_context»⟩)
      start (.success (.of out)) fin) :
    out.GLOBALS = [] := by
  cases h with
  | call hbody =>
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses
          (SpecTec.«$empty_context_clauses»))
        start (.success (.of out)) fin at hbody
      cases hbody with
      | orElse_success hclause =>
          unfold SpecTec.«$empty_context:clause:0» at hclause
          cases hclause with
          | bind_success _ hpure =>
              cases hpure with
              | pure => rfl
      | orElse_unmatch hfailedSupply hnone => restore_supply hfailedSupply at hnone; cases hnone

theorem empty_context_no_bot_candidate
    (out : SpecTec.context) (start fin : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.«$empty_context»⟩)
      start (.success (.of out)) fin) :
    SpecTec.valtype.BotT ∉
      FiniteValidTypes.candidateUniverse out := by
  intro hb
  obtain ⟨m, hm⟩ := (bot_mem_candidate_iff out).1 hb
  rw [empty_context_globals_nil out start fin h] at hm
  simp at hm

end properties.wasm_module_ok.ConstCandidateBot
