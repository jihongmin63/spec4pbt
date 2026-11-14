import WasmConstantSpecification

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 6000000

namespace RustWasm
open SpecTecExecution

def passiveDatum (payload : String) : SpecTec.data := ⟨payload, .Passive⟩

def passiveFree : SpecTec.free :=
  ⟨.«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» [],
    .«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» [], .«`{ % `}» []⟩

def passiveContext (context : SpecTec.context) (payloads : List String) : SpecTec.context :=
  payloads.foldl (fun current _ => { current with DATAS := current.DATAS ++ [.OK] }) context

theorem passive_free_execute (payload : String) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨SpecTec.free, SpecTec.Call.«$free_data» (passiveDatum payload)⟩)
      supply (.success (.of passiveFree)) supply := by
  constant_spec_run

theorem passive_free_list_execute (payloads : List String) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨SpecTec.free,
      SpecTec.Call.«$free_list» SpecTec.data SpecTec.Call.«$free_data» (payloads.map passiveDatum)⟩)
      supply (.success (.of passiveFree)) supply := by
  induction payloads with
  | nil => constant_spec_run
  | cons payload rest ih =>
      apply Eval.call
      apply Eval.orElse_unmatch
      · apply Eval.bind_unmatch
        apply Eval.guard_false
        exact of_decide_eq_true rfl
      · apply Eval.orElse_success
        apply Eval.bind_success
        · apply Eval.guard_true
          exact of_decide_eq_true rfl
        · apply Eval.bind_success
          · exact passive_free_execute payload supply
          · apply Eval.bind_success
            · exact ih
            · constant_spec_run

theorem passive_data_execute (context : SpecTec.context) (payload : String) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨SpecTec.context, SpecTec.Call.Data_ok context (passiveDatum payload)⟩)
      supply (.success (.of { context with DATAS := context.DATAS ++ [SpecTec.datatype.OK] })) supply := by
  constant_spec_run

theorem passive_datas_execute (context : SpecTec.context) (payloads : List String) (supply : Nat) :
    Eval SpecTec.Body (.call ⟨SpecTec.context, SpecTec.Call.Datas_ok context (payloads.map passiveDatum)⟩)
      supply (.success (.of (passiveContext context payloads))) supply := by
  induction payloads generalizing context with
  | nil => constant_spec_run
  | cons payload rest ih =>
      apply Eval.call
      apply Eval.orElse_success
      apply Eval.bind_success
      · apply Eval.guard_true
        exact of_decide_eq_true rfl
      · apply Eval.bind_success
        · exact passive_data_execute context payload supply
        · apply Eval.bind_success
          · exact ih { context with DATAS := context.DATAS ++ [.OK] }
          · exact Eval.pure _

syntax "passive_spec_run" : tactic
macro_rules
| `(tactic| passive_spec_run) => `(tactic|
  first
  | exact passive_free_list_execute _ _
  | exact passive_datas_execute _ _ _
  | exact Eval.pure _
  | exact Eval.unmatch
  | (apply Eval.guard_true; exact of_decide_eq_true rfl)
  | (apply Eval.guard_false; exact of_decide_eq_true rfl)
  | (apply Eval.call; passive_spec_run)
  | (apply Eval.bind_success; passive_spec_run; passive_spec_run)
  | (apply Eval.bind_unmatch; passive_spec_run)
  | (apply Eval.orElse_success; passive_spec_run)
  | (apply Eval.orElse_unmatch; passive_spec_run; passive_spec_run))

def passiveModule (payloads : List String) : SpecTec.module :=
  { emptyModule with DATAS := payloads.map passiveDatum }

theorem passive_module_ok (payloads : List String) : SpecTec.Module_ok (passiveModule payloads) := by
  refine ⟨0, ?_⟩
  passive_spec_run

end RustWasm
