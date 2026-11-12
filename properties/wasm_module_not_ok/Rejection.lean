import properties.wasm_module_not_ok.bundle.Contract
import properties.wasm_module_ok.Execution

set_option autoImplicit false

namespace properties.wasm_module_not_ok.Rejection

theorem not_module_ok_iff_no_success (m : SpecTec.module) :
    ¬ SpecTec.Module_ok m ↔
      ∀ finalSupply : Nat,
        ¬ SpecTecExecution.Eval SpecTec.Body
          (.call ⟨Unit, SpecTec.Call.Module_ok m⟩) 0
          (.success (.of ())) finalSupply := by
  simp only [SpecTec.Module_ok, not_exists]


theorem module_unmatch_invalid (m : SpecTec.module) (finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Module_ok m⟩) 0
      .unmatch finalSupply) :
    ¬ SpecTec.Module_ok m := by
  intro hok
  obtain ⟨successFinal, hs⟩ := hok
  have heq := (properties.wasm_module_ok.Execution.eval_deterministic h hs).1
  cases heq

theorem module_abort_invalid (m : SpecTec.module)
    (message : String) (finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit, SpecTec.Call.Module_ok m⟩) 0
      (.abort message) finalSupply) :
    ¬ SpecTec.Module_ok m := by
  intro hok
  obtain ⟨successFinal, hs⟩ := hok
  have heq := (properties.wasm_module_ok.Execution.eval_deterministic h hs).1
  cases heq

private theorem singleton_clause_success_inv
    {clause : SpecTecExecution.Action.{1} SpecTec.Request}
    {start finalSupply : Nat} {value : SpecTecExecution.Value}
    (h : SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses [clause]) start
      (.success value) finalSupply) :
    SpecTecExecution.Eval SpecTec.Body
      clause start (.success value) finalSupply := by
  change SpecTecExecution.Eval SpecTec.Body
    (.orElse clause (fun _ => .unmatch)) start
    (.success value) finalSupply at h
  cases h with
  | orElse_success hc => exact hc
  | orElse_unmatch hfailedSupply htail => restore_supply hfailedSupply at htail; cases htail

theorem module_clause_success_iff (m : SpecTec.module) :
    SpecTec.Module_ok m ↔
      ∃ finalSupply : Nat,
        SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Module_ok:clause:0» m) 0
          (.success (.of ())) finalSupply := by
  constructor
  · intro hok
    change ∃ finalSupply : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Module_ok m⟩) 0
        (.success (.of ())) finalSupply at hok
    obtain ⟨finalSupply, heval⟩ := hok
    cases heval with
    | call hbody =>
      refine ⟨finalSupply, ?_⟩
      change SpecTecExecution.Eval SpecTec.Body
        (SpecTecExecution.tryClauses (SpecTec.Module_ok_clauses m)) 0
        (.success (.of ())) finalSupply at hbody
      simpa only [SpecTec.Module_ok_clauses] using
        (singleton_clause_success_inv hbody)
  · rintro ⟨finalSupply, hclause⟩
    change ∃ finalSupply : Nat,
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨Unit, SpecTec.Call.Module_ok m⟩) 0
        (.success (.of ())) finalSupply
    refine ⟨finalSupply, SpecTecExecution.Eval.call ?_⟩
    change SpecTecExecution.Eval SpecTec.Body
      (SpecTecExecution.tryClauses (SpecTec.Module_ok_clauses m)) 0
      (.success (.of ())) finalSupply
    simpa only [SpecTec.Module_ok_clauses] using
      (SpecTecExecution.tryClauses_cons_success
        (clause := SpecTec.«Module_ok:clause:0» m)
        (rest := []) hclause)

theorem not_module_ok_iff_no_clause_success (m : SpecTec.module) :
    ¬ SpecTec.Module_ok m ↔
      ∀ finalSupply : Nat,
        ¬ SpecTecExecution.Eval SpecTec.Body
          (SpecTec.«Module_ok:clause:0» m) 0
          (.success (.of ())) finalSupply := by
  rw [module_clause_success_iff]
  simp only [not_exists]

def moduleWithoutCode (m : SpecTec.module) : SpecTec.module :=
  { { m with FUNCS := [] } with START := none }

theorem module_ok_implies_free_success (m : SpecTec.module)
    (hok : SpecTec.Module_ok m) :
    ∃ (free : SpecTec.free) (middle : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.free, SpecTec.Call.«$free_module» (moduleWithoutCode m)⟩)
        0 (.success (.of free)) middle := by
  obtain ⟨finalSupply, hclause⟩ := (module_clause_success_iff m).mp hok
  unfold SpecTec.«Module_ok:clause:0» at hclause
  cases hclause with
  | bind_success hfirst _ => exact ⟨_, _, hfirst⟩


theorem module_not_ok_of_free_unmatch (m : SpecTec.module) (finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_module» (moduleWithoutCode m)⟩)
      0 .unmatch finalSupply) :
    ¬ SpecTec.Module_ok m := by
  intro hok
  obtain ⟨_, _, hs⟩ := module_ok_implies_free_success m hok
  have heq := (properties.wasm_module_ok.Execution.eval_deterministic h hs).1
  cases heq

theorem module_not_ok_of_free_abort (m : SpecTec.module)
    (message : String) (finalSupply : Nat)
    (h : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_module» (moduleWithoutCode m)⟩)
      0 (.abort message) finalSupply) :
    ¬ SpecTec.Module_ok m := by
  intro hok
  obtain ⟨_, _, hs⟩ := module_ok_implies_free_success m hok
  have heq := (properties.wasm_module_ok.Execution.eval_deterministic h hs).1
  cases heq


theorem module_ok_initial_three_calls (m : SpecTec.module)
    (hok : SpecTec.Module_ok m) :
    ∃ (free : SpecTec.free) (c c0 : SpecTec.context)
      (n1 n2 n3 : Nat),
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.free, SpecTec.Call.«$free_module» (moduleWithoutCode m)⟩)
        0 (.success (.of free)) n1 ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context, SpecTec.Call.«$empty_context»⟩)
        n1 (.success (.of c)) n2 ∧
      SpecTecExecution.Eval SpecTec.Body
        (.call ⟨SpecTec.context, SpecTec.Call.Types_ok {c with REFS := free} m.TYPES⟩)
        n2 (.success (.of c0)) n3 := by
  obtain ⟨finalSupply, hclause⟩ := (module_clause_success_iff m).mp hok
  cases hclause with
  | bind_success hfree htail =>
    cases htail with
    | bind_success hempty htail =>
      cases htail with
      | bind_success htypes _ =>
        exact ⟨_, _, _, _, _, _, hfree, hempty, htypes⟩


private theorem value_of_inj_same {α : Type} {x y : α}
    (h : SpecTecExecution.Value.of x = SpecTecExecution.Value.of y) : x = y := by
  cases h
  rfl

theorem module_not_ok_of_types_unmatch (m : SpecTec.module)
    (free : SpecTec.free) (c : SpecTec.context)
    (n1 n2 failedFinal : Nat)
    (hfree : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_module» (moduleWithoutCode m)⟩)
      0 (.success (.of free)) n1)
    (hempty : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.«$empty_context»⟩)
      n1 (.success (.of c)) n2)
    (htypes : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Types_ok {c with REFS := free} m.TYPES⟩)
      n2 .unmatch failedFinal) :
    ¬ SpecTec.Module_ok m := by
  intro hok
  obtain ⟨free', c', c0', n1', n2', n3', hfree', hempty', htypes'⟩ :=
    module_ok_initial_three_calls m hok
  have df := properties.wasm_module_ok.Execution.eval_deterministic hfree hfree'
  have efree : free = free' := value_of_inj_same (by cases df.1; rfl)
  have en1 : n1 = n1' := df.2
  subst free'
  subst n1'
  have de := properties.wasm_module_ok.Execution.eval_deterministic hempty hempty'
  have ec : c = c' := value_of_inj_same (by cases de.1; rfl)
  have en2 : n2 = n2' := de.2
  subst c'
  subst n2'
  have dt := properties.wasm_module_ok.Execution.eval_deterministic htypes htypes'
  cases dt.1

theorem module_not_ok_of_types_abort (m : SpecTec.module)
    (free : SpecTec.free) (c : SpecTec.context)
    (message : String) (n1 n2 failedFinal : Nat)
    (hfree : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.free, SpecTec.Call.«$free_module» (moduleWithoutCode m)⟩)
      0 (.success (.of free)) n1)
    (hempty : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context, SpecTec.Call.«$empty_context»⟩)
      n1 (.success (.of c)) n2)
    (htypes : SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.context,
        SpecTec.Call.Types_ok {c with REFS := free} m.TYPES⟩)
      n2 (.abort message) failedFinal) :
    ¬ SpecTec.Module_ok m := by
  intro hok
  obtain ⟨free', c', c0', n1', n2', n3', hfree', hempty', htypes'⟩ :=
    module_ok_initial_three_calls m hok
  have df := properties.wasm_module_ok.Execution.eval_deterministic hfree hfree'
  have efree : free = free' := value_of_inj_same (by cases df.1; rfl)
  have en1 : n1 = n1' := df.2
  subst free'
  subst n1'
  have de := properties.wasm_module_ok.Execution.eval_deterministic hempty hempty'
  have ec : c = c' := value_of_inj_same (by cases de.1; rfl)
  have en2 : n2 = n2' := de.2
  subst c'
  subst n2'
  have dt := properties.wasm_module_ok.Execution.eval_deterministic htypes htypes'
  cases dt.1


end properties.wasm_module_not_ok.Rejection
