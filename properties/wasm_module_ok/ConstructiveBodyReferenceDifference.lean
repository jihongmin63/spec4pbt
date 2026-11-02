import properties.wasm_module_ok.ConstructiveBodyReferenceProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyReferenceDifference
open SpecTec properties.wasm_module_ok

def difference : reftype → reftype → reftype
  | .«% %» nu heap,.«% %» .Null _ => .«% %» .NoNull heap
  | first,.«% %» .NoNull _ => first

theorem total (a b : reftype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.specTecProgram
      (.call ⟨reftype,SpecTecCall.«$diff_reftype» a b⟩) n (.success (.of (difference a b))) n := by
  cases a with | «% %» na ha =>
   cases b with | «% %» nb hb =>
    apply SpecTecExecution.Eval.call
    change SpecTecExecution.Eval SpecTec.specTecProgram
      (SpecTecExecution.firstSuccess (SpecTec.«$diff_reftype_clauses» (.«% %» na ha) (.«% %» nb hb)) ()) n _ n
    cases nb with
    | Null =>
      apply SpecTecExecution.firstSuccess_cons_success
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
    | NoNull =>
      apply SpecTecExecution.firstSuccess_cons_unmatch
      · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:null:Null»]))
      apply SpecTecExecution.firstSuccess_cons_success
      exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)

theorem backed (c : context) (a b : reftype) (ha : CandidateValMatch.InTableVal c (.RefT a)) :
    CandidateValMatch.InTableVal c (.RefT (difference a b)) := by
  cases a with | «% %» na ha' =>
   cases b with | «% %» nb hb =>
    cases nb <;> exact ha

#print axioms total
end properties.wasm_module_ok.ConstructiveBodyReferenceDifference
