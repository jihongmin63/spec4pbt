import WasmMemoryRepresentation

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace RustWasm
open SpecTecExecution

private theorem selected_clause_execution
    {clauses : List (Action SpecTec.Request)} {start index finish : Nat} {value : Value}
    (selected : Selected SpecTec.Body clauses start index value finish) :
    ∃ clause ∈ clauses, ∃ supply,
      Eval SpecTec.Body clause supply (.success value) finish := by
  induction selected with
  | here run => exact ⟨_, by simp, _, run⟩
  | next _ _ ih =>
      obtain ⟨clause, present, supply, run⟩ := ih
      exact ⟨clause, by simp [present], supply, run⟩

/-- Original memory validity does not depend on the surrounding module context. -/
theorem memtype_valid_of_execution (source target : SpecTec.context) (type : SpecTec.memtype)
    (start finish : Nat)
    (run : Eval SpecTec.Body (.call ⟨Unit, SpecTec.Call.Memtype_ok source type⟩)
      start (.success (.of ())) finish) :
    SpecTec.Memtype_ok target type := by
  cases type with
  | MemoryT address limits =>
      have bounded := memtype_bounds_of_execution source address limits start finish run
      refine ⟨0, ?_⟩
      apply Eval.call
      cases address with
      | I32AT =>
          apply Eval.orElse_success
          apply Eval.bind_success
          · exact Eval.guard_true rfl
          · apply Eval.bind_success
            · exact memory_limits_valid target 65536 limits.MIN limits.MAX 0 bounded
            · exact Eval.pure ()
      | I64AT =>
          apply Eval.orElse_unmatch
          · apply Eval.bind_unmatch
            exact Eval.guard_false (by decide)
          · apply Eval.orElse_success
            apply Eval.bind_success
            · exact Eval.guard_true rfl
            · apply Eval.bind_success
              · exact memory_limits_valid target 281474976710656 limits.MIN limits.MAX 0 bounded
              · exact Eval.pure ()

/-- Extract the type check from the actual successful original import clause. -/
theorem import_memory_type_valid (source target output : SpecTec.context)
    (entry : SpecTec.«import») (type : SpecTec.memtype)
    (descriptor : entry.IDESC = .MemImport type) (start finish : Nat)
    (run : Eval SpecTec.Body (.call ⟨SpecTec.context, SpecTec.Call.Import_ok source entry⟩)
      start (.success (.of output)) finish) :
    SpecTec.Memtype_ok target type := by
  cases run with
  | call body =>
      change Eval SpecTec.Body (tryClauses (SpecTec.Import_ok_clauses source entry))
        start (.success (.of output)) finish at body
      obtain ⟨index, selected⟩ := (tryClauses_success_iff _ _ _ _).mp body
      obtain ⟨clause, present, supply, checked⟩ := selected_clause_execution selected
      simp only [SpecTec.Import_ok_clauses, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl | rfl | rfl
      · unfold SpecTec.«Import_ok:clause:0» at checked
        rw [descriptor] at checked
        cases checked with
        | bind_success guard _ => cases guard with | guard_true impossible => cases impossible
      · unfold SpecTec.«Import_ok:clause:1» at checked
        rw [descriptor] at checked
        cases checked with
        | bind_success guard _ => cases guard with | guard_true impossible => cases impossible
      · unfold SpecTec.«Import_ok:clause:2» at checked
        rw [descriptor] at checked
        cases checked with
        | bind_success guard _ => cases guard with | guard_true impossible => cases impossible
      · unfold SpecTec.«Import_ok:clause:3» at checked
        rw [descriptor] at checked
        cases checked with
        | bind_success _ tail =>
            cases tail with
            | bind_success typed _ => exact memtype_valid_of_execution source target type _ _ typed
      · unfold SpecTec.«Import_ok:clause:4» at checked
        rw [descriptor] at checked
        cases checked with
        | bind_success guard _ => cases guard with | guard_true impossible => cases impossible

/-- Every memory descriptor in a successful original import list is valid. -/
theorem imports_memory_types_valid (source target output : SpecTec.context)
    (items : List SpecTec.«import») (start finish : Nat)
    (run : Eval SpecTec.Body (.call ⟨SpecTec.context, SpecTec.Call.Imports_ok source items⟩)
      start (.success (.of output)) finish) :
    ∀ entry ∈ items, ∀ type, entry.IDESC = .MemImport type → SpecTec.Memtype_ok target type := by
  induction items generalizing source output start finish with
  | nil => simp
  | cons head tail ih =>
      cases run with
      | call body =>
          change Eval SpecTec.Body (tryClauses (SpecTec.Imports_ok_clauses source (head :: tail)))
            start (.success (.of output)) finish at body
          obtain ⟨index, selected⟩ := (tryClauses_success_iff _ _ _ _).mp body
          obtain ⟨clause, present, supply, checked⟩ := selected_clause_execution selected
          simp only [SpecTec.Imports_ok_clauses, List.mem_cons, List.not_mem_nil, or_false] at present
          rcases present with rfl | rfl
          · unfold SpecTec.«Imports_ok:clause:0» at checked
            cases checked with
            | bind_success _ rest =>
                cases rest with
                | bind_success headRun rest =>
                    cases rest with
                    | bind_success tailRun _ =>
                        intro entry present type descriptor
                        rcases List.mem_cons.mp present with rfl | present
                        · exact import_memory_type_valid source target _ entry type descriptor _ _ headRun
                        · exact ih _ _ _ _ tailRun entry present type descriptor
          · unfold SpecTec.«Imports_ok:clause:1» at checked
            cases checked with
            | bind_success guard _ =>
                cases guard with
                | guard_true impossible => simp at impossible

/-- Module validation contains a successful import stage, regardless of preceding stages. -/
theorem module_imports_execution (module : SpecTec.module) (valid : SpecTec.Module_ok module) :
    ∃ (source output : SpecTec.context) (start finish : Nat),
      Eval SpecTec.Body (.call ⟨SpecTec.context, SpecTec.Call.Imports_ok source module.IMPORTS⟩)
        start (.success (.of output)) finish := by
  obtain ⟨finish, run⟩ := valid
  cases run with
  | call body =>
      change Eval SpecTec.Body (tryClauses (SpecTec.Module_ok_clauses module))
        0 (.success (.of ())) finish at body
      obtain ⟨index, selected⟩ := (tryClauses_success_iff _ _ _ _).mp body
      obtain ⟨clause, present, supply, checked⟩ := selected_clause_execution selected
      simp only [SpecTec.Module_ok_clauses, List.mem_singleton] at present
      subst clause
      cases checked with
      | bind_success _ tail =>
          cases tail with
          | bind_success _ tail =>
              cases tail with
              | bind_success _ tail =>
                  cases tail with
                  | bind_success importsRun _ => exact ⟨_, _, _, _, importsRun⟩

end RustWasm
