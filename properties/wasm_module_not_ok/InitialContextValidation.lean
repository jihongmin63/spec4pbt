import properties.wasm_module_not_ok.Rejection

set_option autoImplicit false
namespace properties.wasm_module_not_ok.Rejection

theorem empty_set_total (K : Type) (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.set K, SpecTec.SpecTecCall.«$empty_set» K⟩)
      start (.success (.of (SpecTec.set.«`{ % `}» ([] : List K)))) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$empty_set_clauses» K) ())
    start (.success (.of (SpecTec.set.«`{ % `}» ([] : List K)))) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$empty_set:clause:0» K)
    start (.success (.of (SpecTec.set.«`{ % `}» ([] : List K)))) start
  exact SpecTecExecution.Eval.pure _


def emptyFree : SpecTec.free :=
  { TYPES := .«`{ % `}» [], GLOBALS := .«`{ % `}» [],
    TABLES := .«`{ % `}» [], MEMS := .«`{ % `}» [],
    TAGS := .«`{ % `}» [], FUNCS := .«`{ % `}» [],
    ELEMS := .«`{ % `}» [], DATAS := .«`{ % `}» [],
    LOCALS := .«`{ % `}» [], LABELS := .«`{ % `}» [] }

theorem free_empty_total (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.free, SpecTec.SpecTecCall.«$free_empty»⟩)
      start (.success (.of emptyFree)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess SpecTec.«$free_empty_clauses» ())
    start (.success (.of emptyFree)) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    SpecTec.«$free_empty:clause:0»
    start (.success (.of emptyFree)) start
  unfold SpecTec.«$free_empty:clause:0»
  apply SpecTecExecution.Eval.bind_success (empty_set_total _ start)
  apply SpecTecExecution.Eval.bind_success (empty_set_total _ start)
  apply SpecTecExecution.Eval.bind_success (empty_set_total _ start)
  apply SpecTecExecution.Eval.bind_success (empty_set_total _ start)
  apply SpecTecExecution.Eval.bind_success (empty_set_total _ start)
  apply SpecTecExecution.Eval.bind_success (empty_set_total _ start)
  apply SpecTecExecution.Eval.bind_success (empty_set_total _ start)
  apply SpecTecExecution.Eval.bind_success (empty_set_total _ start)
  apply SpecTecExecution.Eval.bind_success (empty_set_total _ start)
  apply SpecTecExecution.Eval.bind_success (empty_set_total _ start)
  exact SpecTecExecution.Eval.pure emptyFree


def emptyContext : SpecTec.context :=
  { TYPES := [], FUNCS := [], TABLES := [], MEMS := [], TAGS := [],
    GLOBALS := [], ELEMS := [], DATAS := [], LOCALS := [],
    RESULTS := [], LABELS := [], REFS := emptyFree }

theorem empty_context_total (start : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.«$empty_context»⟩)
      start (.success (.of emptyContext)) start := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess SpecTec.«$empty_context_clauses» ())
    start (.success (.of emptyContext)) start
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    SpecTec.«$empty_context:clause:0»
    start (.success (.of emptyContext)) start
  unfold SpecTec.«$empty_context:clause:0»
  apply SpecTecExecution.Eval.bind_success (free_empty_total start)
  exact SpecTecExecution.Eval.pure emptyContext

theorem empty_context_deterministic (start finalSupply : Nat)
    (outcome : SpecTecExecution.Outcome SpecTecExecution.Value)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.context, SpecTec.SpecTecCall.«$empty_context»⟩)
      start outcome finalSupply) :
    outcome = .success (.of emptyContext) ∧ finalSupply = start :=
  SpecTecExecution.eval_deterministic program_primitive_deterministic h
    (empty_context_total start)

end properties.wasm_module_not_ok.Rejection
