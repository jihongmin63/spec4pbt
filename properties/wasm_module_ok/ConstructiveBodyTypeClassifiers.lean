import properties.wasm_module_ok.ConstructiveBodyReferenceCalls
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyTypeClassifiers
open SpecTec properties.wasm_module_ok

def numeric : valtype → Bool
  | .NumT _ | .BotT => true
  | _ => false
def vector : valtype → Bool
  | .VecT _ | .BotT => true
  | _ => false

theorem numeric_total (t : valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$is_num_type» t⟩) n (.success (.of (numeric t))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$is_num_type_clauses» t) ()) n _ n
  cases t
  all_goals
    repeat
      first
      | apply SpecTecExecution.firstSuccess_cons_success
        first
        | exact SpecTecExecution.Eval.pure _
        | exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
      | apply SpecTecExecution.firstSuccess_cons_unmatch
        · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:valtype:NumT»,SpecTec.«exec:match:valtype:VecT»,SpecTec.«exec:match:valtype:BotT»]))

theorem vector_total (t : valtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨Bool,SpecTecCall.«$is_vec_type» t⟩) n (.success (.of (vector t))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.specTecProgram
    (SpecTecExecution.firstSuccess (SpecTec.«$is_vec_type_clauses» t) ()) n _ n
  cases t
  all_goals
    repeat
      first
      | apply SpecTecExecution.firstSuccess_cons_success
        first
        | exact SpecTecExecution.Eval.pure _
        | exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
      | apply SpecTecExecution.firstSuccess_cons_unmatch
        · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by
            simp [SpecTec.«exec:match:valtype:NumT»,SpecTec.«exec:match:valtype:VecT»,SpecTec.«exec:match:valtype:BotT»]))

#print axioms numeric_total
#print axioms vector_total
end properties.wasm_module_ok.ConstructiveBodyTypeClassifiers
