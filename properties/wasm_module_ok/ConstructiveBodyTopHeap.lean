import properties.wasm_module_ok.ConstructiveBodyReferenceProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyTopHeap
open SpecTec properties.wasm_module_ok

def basePairs : List (heaptype × heaptype) :=
  [(.AnyHT,.AnyHT),(.NoneHT,.AnyHT),(.EqHT,.AnyHT),(.StructHT,.AnyHT),(.ArrayHT,.AnyHT),(.I31HT,.AnyHT),
   (.FuncHT,.FuncHT),(.NoFuncHT,.FuncHT),(.ExnHT,.ExnHT),(.NoExnHT,.ExnHT),(.ExternHT,.ExternHT),(.NoExternHT,.ExternHT)]

theorem base_call (c : context) (heap top : heaptype) (n : Nat) (hp : (heap,top)∈basePairs) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨heaptype,Call.«$top_of_heap_type» c.TYPES heap⟩) n (.success (.of top)) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.«$top_of_heap_type_clauses» c.TYPES heap)) n _ n
  simp only [basePairs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp|hp <;> cases hp
  all_goals
    repeat
      first
      | apply SpecTecExecution.tryClauses_cons_success
        exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (by decide)) (SpecTecExecution.Eval.pure _)
      | apply SpecTecExecution.tryClauses_cons_unmatch
        · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by decide))

def abstraction : strtype → heaptype
  | .DefStructT _ => .StructHT
  | .DefArrayT _ => .ArrayHT
  | .DefFuncT _ => .FuncHT

def structuralTop : strtype → heaptype
  | .DefFuncT _ => .FuncHT
  | _ => .AnyHT

theorem abstraction_call (st : strtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨heaptype,Call.«$abs_of_str_type» st⟩) n (.success (.of (abstraction st))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.«$abs_of_str_type_clauses» st)) n _ n
  cases st
  all_goals
    repeat
      first
      | apply SpecTecExecution.tryClauses_cons_success
        exact SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl) (SpecTecExecution.Eval.pure _)
      | apply SpecTecExecution.tryClauses_cons_unmatch
        · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:strtype:DefStructT»,SpecTec.«exec:match:strtype:DefArrayT»,SpecTec.«exec:match:strtype:DefFuncT»]))

theorem structural_call (c : context) (st : strtype) (n : Nat) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨heaptype,Call.«$top_of_str_type» c.TYPES st⟩) n (.success (.of (structuralTop st))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.«$top_of_str_type_clauses» c.TYPES st)) n _ n
  apply SpecTecExecution.tryClauses_cons_success
  apply SpecTecExecution.Eval.bind_success (abstraction_call st n)
  apply SpecTecExecution.Eval.bind_success (base_call c (abstraction st) (structuralTop st) n (by cases st <;> simp [basePairs,abstraction,structuralTop]))
  exact SpecTecExecution.Eval.pure _

theorem static_call (c : context) (x : Nat) (dt : deftype) (st : strtype) (n : Nat)
    (hx : c.TYPES[x]?=some dt) (he : UnrollInterface.expandResult dt=some st) :
    SpecTecExecution.Eval SpecTec.Body
      (.call ⟨heaptype,Call.«$top_of_heap_type» c.TYPES (.VarHT (.StatX x))⟩)
      n (.success (.of (structuralTop st))) n := by
  apply SpecTecExecution.Eval.call
  change SpecTecExecution.Eval SpecTec.Body
    (SpecTecExecution.tryClauses (SpecTec.«$top_of_heap_type_clauses» c.TYPES (.VarHT (.StatX x)))) n _ n
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp))
  apply SpecTecExecution.tryClauses_cons_unmatch
  · exact SpecTecExecution.Eval.bind_unmatch (SpecTecExecution.Eval.guard_false (by simp [SpecTec.«exec:match:heaptype:DefHT»]))
  apply SpecTecExecution.tryClauses_cons_success
  change SpecTecExecution.Eval SpecTec.Body (SpecTec.«$top_of_heap_type:clause:5» c.TYPES (.VarHT (.StatX x))) n _ n
  unfold SpecTec.«$top_of_heap_type:clause:5»
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true rfl)
  apply SpecTecExecution.Eval.bind_success (SpecTecExecution.Eval.guard_true (List.getElem?_eq_some_iff.mp hx).1)
  rw [hx]
  apply SpecTecExecution.Eval.bind_success ((UnrollInterface.expanddt_success_iff_result dt st n n).2 ⟨he,rfl⟩)
  apply SpecTecExecution.Eval.bind_success (structural_call c st n)
  exact SpecTecExecution.Eval.pure _

#print axioms static_call
end properties.wasm_module_ok.ConstructiveBodyTopHeap
