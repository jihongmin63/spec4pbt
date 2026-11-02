import properties.wasm_module_ok.bundle.Helpers
import properties.wasm_module_ok.MatchResulttypeValidation

set_option autoImplicit false

namespace properties.wasm_module_ok.BotMatchValidation

theorem match_valtype_bot_total
    (types : List SpecTec.deftype) (t : SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool, SpecTec.SpecTecCall.«$match_valtype»
        types .BotT t⟩)
      n (.success (.of true)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess
      (SpecTec.«$match_valtype_clauses» types .BotT t) ())
    n (.success (.of true)) n
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_valtype:clause:0» types .BotT t)
      n .unmatch n
    unfold SpecTec.«$match_valtype:clause:0»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:valtype:NumT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_valtype:clause:1» types .BotT t)
      n .unmatch n
    unfold SpecTec.«$match_valtype:clause:1»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:valtype:VecT»]))
  apply SpecTecExecution.firstSuccess_cons_unmatch
  · change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTec.«$match_valtype:clause:2» types .BotT t)
      n .unmatch n
    unfold SpecTec.«$match_valtype:clause:2»
    exact SpecTecExecution.Eval.bind_unmatch
      (SpecTecExecution.Eval.guard_false
        (by simp [SpecTec.«exec:match:valtype:RefT»]))
  apply SpecTecExecution.firstSuccess_cons_success
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTec.«$match_valtype:clause:3» types .BotT t)
    n (.success (.of true)) n
  unfold SpecTec.«$match_valtype:clause:3»
  apply SpecTecExecution.Eval.bind_success
  · exact SpecTecExecution.Eval.guard_true rfl
  exact SpecTecExecution.Eval.pure true

theorem match_iter_bot_list_total
    (c : SpecTec.context) (ts : List SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit,
        SpecTec.SpecTecCall.«Match_resulttype:rule:iter:0»
          c (List.replicate ts.length .BotT) ts⟩)
      n (.success (.of ())) n := by
  induction ts with
  | nil =>
      simpa using MatchResulttypeValidation.match_iter_nil_total c n
  | cons t rest ih =>
      simpa only [List.length_cons, List.replicate_succ] using
        ((MatchResulttypeValidation.match_iter_cons_success_iff
          c .BotT t (List.replicate rest.length .BotT) rest n n).2
          ⟨n, match_valtype_bot_total c.TYPES t n, ih⟩)

theorem match_resulttype_bot_list_total
    (c : SpecTec.context) (ts : List SpecTec.valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Unit, SpecTec.SpecTecCall.Match_resulttype c
        (List.replicate ts.length .BotT) ts⟩)
      n (.success (.of ())) n := by
  apply (MatchResulttypeValidation.match_resulttype_success_iff
    c (List.replicate ts.length .BotT) ts n n).2
  exact ⟨by simp, match_iter_bot_list_total c ts n⟩

end properties.wasm_module_ok.BotMatchValidation
