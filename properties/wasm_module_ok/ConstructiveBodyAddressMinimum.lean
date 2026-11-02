import properties.wasm_module_ok.ConstructiveBodyIndexedCalls
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyAddressMinimum
open SpecTec properties.wasm_module_ok

def minimum : addrtype → addrtype → addrtype
  | .I64AT,.I64AT => .I64AT
  | _,_ => .I32AT

theorem total (a b : addrtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨addrtype,SpecTecCall.«$min_addrtype» a b⟩) n (.success (.of (minimum a b))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$min_addrtype_clauses» a b) ()) n _ n
  by_cases h : a=.I64AT ∧ b=.I64AT
  · rcases h with ⟨rfl,rfl⟩
    apply SpecTecExecution.firstSuccess_cons_success
    exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true ⟨rfl,rfl⟩)
      (SpecTecExecution.Eval.pure _)
  · have he : minimum a b=.I32AT := by cases a <;> cases b <;> simp_all [minimum]
    rw [he]
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false h)
    · apply SpecTecExecution.firstSuccess_cons_success
      exact SpecTecExecution.Eval.pure _

#print axioms total
end properties.wasm_module_ok.ConstructiveBodyAddressMinimum
