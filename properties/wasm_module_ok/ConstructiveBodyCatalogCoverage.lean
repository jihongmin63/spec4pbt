import properties.wasm_module_ok.ConstructiveBodyAtomicCoverage
import properties.wasm_module_ok.ConstructiveBodyChildCoverage
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyCatalogCoverage
open SpecTec properties.wasm_module_ok SpecTecExecution ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveBodyProductionCoverage ConstructiveBodyGeneration

theorem arity_le_size (i : instr) : ConstructiveBodyAtomicCoverage.arity i≤sizeOf i := by
  cases i <;> simp +arith [ConstructiveBodyAtomicCoverage.arity]

theorem original (c : context) (stack : inferresulttype) (env : Env c) (hs : StackBacked c stack)
    (i : instr) (depth : Nat) (hd : ConstructiveBodyAtomicCoverage.arity i≤depth) (child : ConstructiveBodyControlProductions.Builder)
    (hc : ConstructiveBodyChildCoverage.Complete child i) (effect : inferinstrtype) (n finish : Nat)
    (h : Eval SpecTec.specTecProgram (.call ⟨inferinstrtype,SpecTecCall.Instr_ok c stack i⟩)
      n (.success (.of effect)) finish) : Covers (catalog c stack env hs depth child) i effect ∧ finish=n := by
  by_cases ha : ConstructiveBodyAtomicCoverage.Atomic i
  · exact ConstructiveBodyAtomicCoverage.original c stack env hs i ha depth hd child effect n finish h
  · cases i <;> try (exact False.elim (ha trivial))
    case BLOCK bt code =>
      apply ConstructiveBodyAtomicCoverage.lift (ConstructiveBodyChildCoverage.block c stack env child bt code hc effect n finish h)
      intro p hp
      exact List.mem_append_left _ (List.mem_append_right _ hp)
    case LOOP bt code =>
      apply ConstructiveBodyAtomicCoverage.lift (ConstructiveBodyChildCoverage.loop c stack env child bt code hc effect n finish h)
      intro p hp
      exact List.mem_append_left _ (List.mem_append_right _ hp)
    case «IF % % ELSE %» bt yes no =>
      apply ConstructiveBodyAtomicCoverage.lift (ConstructiveBodyChildCoverage.ifElse c stack env child bt yes no hc effect n finish h)
      intro p hp
      exact List.mem_append_left _ (List.mem_append_right _ hp)
    case TRY_TABLE bt handlers code =>
      apply ConstructiveBodyAtomicCoverage.lift (ConstructiveBodyChildCoverage.tryTable c stack env child bt handlers code hc effect n finish h)
      intro p hp
      exact List.mem_append_right _ hp

#print axioms original
end properties.wasm_module_ok.ConstructiveBodyCatalogCoverage
