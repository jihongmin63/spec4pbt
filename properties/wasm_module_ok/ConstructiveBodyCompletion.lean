import properties.wasm_module_ok.UnreachableValidation
import properties.wasm_module_ok.ConstConstructiveTrace

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyCompletion
open properties.wasm_module_ok

/-- Completion consumes any current stack, with no prefix revalidation. -/
theorem pop_unreachable_total (c : SpecTec.context)
    (stack : SpecTec.inferresulttype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype, SpecTec.SpecTecCall.«$pop» c
        (.Ellipses, []) stack⟩)
      n (.success (.of (stack.1, ([] : List SpecTec.valtype)))) n := by
  rcases stack with ⟨ell, ts⟩
  cases ell with
  | Ellipses =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$pop_clauses» c (.Ellipses, []) (.Ellipses, ts)) ())
      n (.success (.of (SpecTec.ellipses.Ellipses, ([] : List SpecTec.valtype)))) n
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$pop:clause:0» c (.Ellipses, []) (.Ellipses, ts))
      n (.success (.of (SpecTec.ellipses.Ellipses, ([] : List SpecTec.valtype)))) n
    unfold SpecTec.«$pop:clause:0»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (MinValidation.min_total 0 ts.length n)
    simp only [Nat.zero_min]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
    simp only [Int.toNat?]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
    apply SpecTecExecution.Eval.bind_success
    · unfold SpecTecExecution.require
      exact SpecTecExecution.Eval.orElse_success
        (SpecTecExecution.Eval.guard_true (by simp))
    apply SpecTecExecution.Eval.bind_success (MakeValidation.make_total SpecTec.valtype .BotT 0 n)
    simp only [MakeValidation.makeResult, List.take_zero, List.nil_append]
    apply SpecTecExecution.Eval.bind_success (MatchResulttypeValidation.match_resulttype_nil_total c n)
    exact SpecTecExecution.Eval.pure _
  | NoEllipses =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess
        (SpecTec.«$pop_clauses» c (.Ellipses, []) (.NoEllipses, ts)) ())
      n (.success (.of (SpecTec.ellipses.NoEllipses, ([] : List SpecTec.valtype)))) n
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$pop:clause:0» c (.Ellipses, []) (.NoEllipses, ts)) n .unmatch n
      unfold SpecTec.«$pop:clause:0»
      apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:ellipses:Ellipses»]))
    apply SpecTecExecution.firstSuccess_cons_unmatch
    · change SpecTecExecution.Eval SpecTec.specTecProgram
        (SpecTec.«$pop:clause:1» c (.Ellipses, []) (.NoEllipses, ts)) n .unmatch n
      unfold SpecTec.«$pop:clause:1»
      exact SpecTecExecution.Eval.bind_unmatch
        (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:ellipses:NoEllipses»]))
    apply SpecTecExecution.firstSuccess_cons_success
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$pop:clause:2» c (.Ellipses, []) (.NoEllipses, ts))
      n (.success (.of (SpecTec.ellipses.NoEllipses, ([] : List SpecTec.valtype)))) n
    unfold SpecTec.«$pop:clause:2»
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
    apply SpecTecExecution.Eval.bind_success (MinValidation.min_total 0 ts.length n)
    simp only [Nat.zero_min]
    apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by simp))
    simp only [Int.toNat?]
    apply SpecTecExecution.Eval.bind_success
    · unfold SpecTecExecution.require
      exact SpecTecExecution.Eval.orElse_success
        (SpecTecExecution.Eval.guard_true (by simp))
    simp only [List.take_zero]
    apply SpecTecExecution.Eval.bind_success (MatchResulttypeValidation.match_resulttype_nil_total c n)
    exact SpecTecExecution.Eval.pure _

/-- All successful original prefixes have an executable one-instruction closure.
This does not assert a generator for the prefixes. -/
theorem prefix_completion (c : SpecTec.context)
    (inputs outputs : List SpecTec.valtype) (locals : List SpecTec.localidx)
    (xs : List SpecTec.instr) (result : SpecTec.inferresulttype × List SpecTec.idx)
    (start finish : Nat)
    (h : SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.SpecTecCall.Instrs_ok c (.NoEllipses, inputs) xs⟩)
      start (.success (.of result)) finish) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Block_ok c
        (.InstrT inputs outputs locals) (xs ++ [.UNREACHABLE])⟩)
      start (.success (.of ())) finish := by
  obtain ⟨_, finalContext, htrace⟩ :=
    (ConstConstructiveTrace.instrs_success_iff_trace
      xs c (.NoEllipses, inputs) result start finish).1 h
  have hclose : ConstConstructiveTrace.Trace finalContext result.1
      [.UNREACHABLE] finalContext (.Ellipses, []) finish finish := by
    apply ConstConstructiveTrace.Trace.cons
      (UnreachableValidation.unreachable_instr_total finalContext result.1 finish)
      (LocalInitValidation.init_locals_nil_total finalContext finish)
      (pop_unreachable_total finalContext result.1 finish)
    · simpa only [PushValidation.pushOutcome, PushValidation.pushResult] using
        (PushValidation.push_total finalContext (.Ellipses, []) (result.1.1, []) finish)
    · exact ConstConstructiveTrace.Trace.nil finalContext (.Ellipses, []) finish
  exact (BlockTrace.block_success_iff c inputs outputs locals
    (xs ++ [SpecTec.instr.UNREACHABLE]) start finish).2 ⟨(.Ellipses, []), [], .Ellipses, finish,
    ConstConstructiveTrace.trace_to_instrs (ConstConstructiveTrace.trace_append htrace hclose),
    UnreachableValidation.pop_ellipsis_empty_total c outputs finish⟩

end properties.wasm_module_ok.ConstructiveBodyCompletion
