import properties.wasm_module_ok.BotMatchValidation
import properties.wasm_module_ok.MakeValidation
import properties.wasm_module_ok.MinValidation
import properties.wasm_module_ok.InstrsValidation
import properties.wasm_module_ok.LocalInitValidation
import properties.wasm_module_ok.PushValidation
import properties.wasm_module_ok.BlockTrace
import properties.wasm_module_ok.FuncbodyTrace

set_option autoImplicit false

namespace properties.wasm_module_ok.UnreachableValidation

theorem makeResult_bot_eq_replicate (n : Nat) :
    MakeValidation.makeResult SpecTec.valtype.BotT n =
      List.replicate n SpecTec.valtype.BotT := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [MakeValidation.makeResult, ih, List.replicate_succ']

theorem pop_ellipsis_empty_clause_total
    (c : SpecTec.context) (ts : List SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$pop:clause:1» c
        (.NoEllipses, ts) (.Ellipses, ([] : List SpecTec.valtype)))
      n (.success (.of
        (SpecTec.ellipses.Ellipses, ([] : List SpecTec.valtype)))) n := by
  unfold SpecTec.«$pop:clause:1»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success
    (MinValidation.min_total ts.length 0 n)
  simp only [Nat.min_zero]
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by simp)
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by simp)
  simp
  apply SpecTecExecution.Eval.bind_success
  · unfold SpecTecExecution.require
    exact SpecTecExecution.Eval.orElse_success
      (SpecTecExecution.Eval.guard_true (by simp))
  apply SpecTecExecution.Eval.bind_success
    (MakeValidation.make_total SpecTec.valtype .BotT ts.length n)
  rw [makeResult_bot_eq_replicate]
  simp only [List.length_nil, Nat.zero_add, List.drop_nil,
    List.take_nil, List.append_nil]
  apply SpecTecExecution.Eval.bind_success
    (BotMatchValidation.match_resulttype_bot_list_total c ts n)
  apply SpecTecExecution.Eval.bind_success
  · unfold SpecTecExecution.require
    exact SpecTecExecution.Eval.orElse_success
      (SpecTecExecution.Eval.guard_true (by simp))
  exact SpecTecExecution.Eval.pure _

theorem pop_ellipsis_empty_total
    (c : SpecTec.context) (ts : List SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.NoEllipses, ts) (.Ellipses, ([] : List SpecTec.valtype))⟩)
      n (.success (.of
        (SpecTec.ellipses.Ellipses, ([] : List SpecTec.valtype)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$pop_clauses» c
        (.NoEllipses, ts) (.Ellipses, ([] : List SpecTec.valtype))))
    n (.success (.of
      (SpecTec.ellipses.Ellipses, ([] : List SpecTec.valtype)))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$pop:clause:0» c
        (.NoEllipses, ts) (.Ellipses, ([] : List SpecTec.valtype)))
      n .unmatch n
    unfold SpecTec.«$pop:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:ellipses:Ellipses»]))
  apply SpecTecExecution.tryClauses_cons_success
  exact pop_ellipsis_empty_clause_total c ts n

theorem unreachable_instr_total
    (c : SpecTec.context) (irt : SpecTec.inferresulttype)
    (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferinstrtype,
        SpecTec.Call.Instr_ok c irt .UNREACHABLE⟩)
      n (.success (.of (({
        INS := (.Ellipses, []), OUTS := (.Ellipses, [])
        } : SpecTec.inferfunctype),
        ([] : List SpecTec.localidx)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.Instr_ok_clauses c irt .UNREACHABLE))
    n (.success (.of (({
      INS := (.Ellipses, []), OUTS := (.Ellipses, [])
      } : SpecTec.inferfunctype),
      ([] : List SpecTec.localidx)))) n
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTec.«Instr_ok:clause:0» c irt .UNREACHABLE)
    n (.success (.of (({
      INS := (.Ellipses, []), OUTS := (.Ellipses, [])
      } : SpecTec.inferfunctype),
      ([] : List SpecTec.localidx)))) n
  unfold SpecTec.«Instr_ok:clause:0»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure _

theorem pop_unreachable_input_clause_total
    (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$pop:clause:2» c
        (.Ellipses, ([] : List SpecTec.valtype))
        (.NoEllipses, ([] : List SpecTec.valtype)))
      n (.success (.of
        (SpecTec.ellipses.NoEllipses, ([] : List SpecTec.valtype)))) n := by
  unfold SpecTec.«$pop:clause:2»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  apply SpecTecExecution.Eval.bind_success
    (MinValidation.min_total 0 0 n)
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true (by decide)
  apply SpecTecExecution.Eval.bind_success
  · unfold SpecTecExecution.require
    exact SpecTecExecution.Eval.orElse_success
      (SpecTecExecution.Eval.guard_true (by decide))
  apply SpecTecExecution.Eval.bind_success
    (MatchResulttypeValidation.match_resulttype_nil_total c n)
  exact SpecTecExecution.Eval.pure _

theorem pop_unreachable_input_total
    (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype,
        SpecTec.Call.«$pop» c
          (.Ellipses, ([] : List SpecTec.valtype))
          (.NoEllipses, ([] : List SpecTec.valtype))⟩)
      n (.success (.of
        (SpecTec.ellipses.NoEllipses, ([] : List SpecTec.valtype)))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses
      (SpecTec.«$pop_clauses» c
        (.Ellipses, ([] : List SpecTec.valtype))
        (.NoEllipses, ([] : List SpecTec.valtype))))
    n (.success (.of
      (SpecTec.ellipses.NoEllipses, ([] : List SpecTec.valtype)))) n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$pop:clause:0» c
        (.Ellipses, ([] : List SpecTec.valtype))
        (.NoEllipses, ([] : List SpecTec.valtype))) n .unmatch n
    unfold SpecTec.«$pop:clause:0»
    apply SpecTecExecution.Eval.bind_success
    · exact SpecTecExecution.Eval.guard_true rfl
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:ellipses:Ellipses»]))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.Body
      (SpecTec.«$pop:clause:1» c
        (.Ellipses, ([] : List SpecTec.valtype))
        (.NoEllipses, ([] : List SpecTec.valtype))) n .unmatch n
    unfold SpecTec.«$pop:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:ellipses:NoEllipses»]))
  apply SpecTecExecution.tryClauses_cons_success
  exact pop_unreachable_input_clause_total c n

theorem instrs_unreachable_total
    (c : SpecTec.context) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨SpecTec.inferresulttype × List SpecTec.idx,
        SpecTec.Call.Instrs_ok c
          (.NoEllipses, ([] : List SpecTec.valtype))
          [.UNREACHABLE]⟩)
      n (.success (.of
        ((SpecTec.ellipses.Ellipses, ([] : List SpecTec.valtype)),
          ([] : List SpecTec.idx)))) n := by
  apply (InstrsValidation.instrs_cons_success_iff
    c (.NoEllipses, []) .UNREACHABLE []
    ((.Ellipses, []), []) n n).2
  refine ⟨(({
    INS := (.Ellipses, []), OUTS := (.Ellipses, [])
    } : SpecTec.inferfunctype),
    ([] : List SpecTec.localidx)),
    c, (.NoEllipses, []), (.Ellipses, []),
    n, n, n, n, ?_, ?_, ?_, ?_, ?_⟩
  · exact unreachable_instr_total c (.NoEllipses, []) n
  · exact LocalInitValidation.init_locals_nil_total c n
  · exact pop_unreachable_input_total c n
  · simpa [PushValidation.pushOutcome, PushValidation.pushResult] using
      (PushValidation.push_total c (.Ellipses, []) (.NoEllipses, []) n)
  · exact InstrsValidation.instrs_nil_total c (.Ellipses, []) n

theorem block_unreachable_total
    (c : SpecTec.context) (ts : List SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Block_ok c
          (.InstrT [] ts []) [.UNREACHABLE]⟩)
      n (.success (.of ())) n := by
  apply (BlockTrace.block_success_iff
    c [] ts [] [.UNREACHABLE] n n).2
  exact ⟨(.Ellipses, []), [], .Ellipses, n,
    instrs_unreachable_total c n,
    pop_ellipsis_empty_total c ts n⟩

theorem funcbody_unreachable_total
    (c : SpecTec.context) (f : SpecTec.func)
    (args results : List SpecTec.valtype) (n : Nat)
    (hft : FunctionTypeValidation.funcTypeResult c f.FTYPE =
      some (.FuncT args results))
    (hloc : LocalListValidation.allLocalsValid c f.LOCALS = true) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨Unit,
        SpecTec.Call.Funcbody_ok c
          {f with BODY := [.UNREACHABLE]}⟩)
      n (.success (.of ())) n := by
  apply (FuncbodyTrace.funcbody_success_iff_precomputed
    c {f with BODY := [.UNREACHABLE]} n n).2
  refine ⟨args, results, ?_, ?_, ?_⟩
  · simpa using hft
  · simpa using hloc
  · exact block_unreachable_total
      (FuncbodyTrace.bodyContext c args results
        (LocalListValidation.localTypes f.LOCALS)) results n

end properties.wasm_module_ok.UnreachableValidation
