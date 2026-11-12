import properties.wasm_module_ok.ConstructiveFreeInstructions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveFreeConstants
open SpecTec SpecTecExecution
open properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open FreeUnionValidation properties.wasm_module_ok.ConstructiveFreeTypes properties.wasm_module_ok.ConstructiveFreeInstructions

/-- A structural, context-free superset of all constant instruction forms. -/
def Flat (i : instr) : Prop :=
  match i with
  | .«REF.NULL» _ | .«REF.FUNC» _ | .«GLOBAL.GET» _ | .«STRUCT.NEW» _ _
  | .«ARRAY.NEW» _ _ | .«ARRAY.NEW_FIXED» _ _ | .CONST _ | .«VEC.CONST» _
  | .«REF.I31» | .«EXTERN.CONVERT» _ | .BINOP _ => True
  | _ => False

theorem syntax_flat (c : context) (i : instr)
    (h : ConstAdditionalSyntaxValidation.Syntax c i) : Flat i := by
  cases h <;> try trivial
  rename_i hi
  simp only [ConstArithmeticValidation.arithmeticOps, List.mem_cons,
    List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem flat_instr_free_total (i : instr) (n : Nat) (h : Flat i) :
    Eval Body (.call ⟨free, Call.«$free_instr» i⟩)
      n (.success (.of (instrFree i))) n := by
  cases i <;> try exact h.elim
  all_goals first
    | exact refNull_free_total _ n
    | exact refFunc_free_total _ n
    | exact globalGet_free_total _ n
    | exact structNew_free_total _ _ n
    | exact arrayNew_free_total _ _ n
    | exact arrayFixed_free_total _ _ n
    | exact num_free_total _ n
    | exact vec_free_total _ n
    | exact i31_free_total n
    | exact extern_free_total _ n
    | exact binop_free_total _ n

@[simp] theorem heaptype_labels (ht : heaptype) :
    (heaptypeFree ht).LABELS = .«`{ % `}» [] := by
  cases ht <;> try rfl
  rename_i tv
  cases tv <;> rfl

@[simp] theorem instr_labels (i : instr) :
    (instrFree i).LABELS = .«`{ % `}» [] := by
  cases i <;> try rfl
  exact heaptype_labels _

@[simp] theorem list_labels (xs : List instr) :
    (listFree instrFree xs).LABELS = .«`{ % `}» [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [listFree, unionFree, instr_labels, ih]
    rfl

theorem flat_list_free_total (xs : List instr) (n : Nat)
    (h : ∀ i ∈ xs, Flat i) :
    Eval Body
      (.call ⟨free, Call.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959» xs⟩)
      n (.success (.of (listFree instrFree xs))) n := by
  induction xs with
  | nil =>
    apply Eval.call
    change Eval Body (tryClauses
      (SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959_clauses» [])) _ _ _
    apply tryClauses_cons_success
    unfold SpecTec.«$free_list:specialized:627ab0672e3a767978c05fd35fc5a959:clause:0»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (free_empty_total n)
    exact Eval.pure _
  | cons i xs ih =>
    apply (free_instr_list_cons_success_iff i xs (listFree instrFree (i::xs)) n n).2
    exact ⟨instrFree i, listFree instrFree xs, n, n,
      flat_instr_free_total i n (h i (by simp)),
      ih (by intro j hj; exact h j (by simp [hj])), fold_left_singleton_total _ _ n⟩

theorem shift_empty_total (n : Nat) :
    Eval Body (.call ⟨set Nat, Call.«$free_shift» (.«`{ % `}» [])⟩)
      n (.success (.of (set.«`{ % `}» ([] : List Nat)))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_shift_clauses» _)) _ _ _
  apply tryClauses_cons_success
  unfold SpecTec.«$free_shift:clause:0»
  apply Eval.bind_success
  · apply Eval.call
    change Eval Body (tryClauses (SpecTec.«$map_set_clauses» Nat Nat
      Call.«$add_minus_one» (.«`{ % `}» []))) _ _ _
    apply tryClauses_cons_success
    unfold SpecTec.«$map_set:clause:0»
    apply Eval.bind_success (Eval.guard_true rfl)
    exact Eval.pure _
  · exact Eval.pure _

def constFree (xs : List instr) : free := listFree instrFree xs

theorem block_free_total (xs : List instr) (n : Nat) (h : ∀ i ∈ xs, Flat i) :
    Eval Body (.call ⟨free, Call.«$free_block» xs⟩)
      n (.success (.of (constFree xs))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_block_clauses» xs)) _ _ _
  apply tryClauses_cons_success
  unfold SpecTec.«$free_block:clause:0»
  apply Eval.bind_success (flat_list_free_total xs n h)
  simp only [list_labels]
  apply Eval.bind_success (shift_empty_total n)
  have heq : ({listFree instrFree xs with LABELS := .«`{ % `}» []} : free) =
      constFree xs := by
    unfold constFree
    rw [← list_labels xs]
  rw [heq]
  exact Eval.pure _

theorem const_free_total (xs : List instr) (n : Nat) (h : ∀ i ∈ xs, Flat i) :
    Eval Body (.call ⟨free, Call.«$free_const» xs⟩)
      n (.success (.of (constFree xs))) n := by
  apply Eval.call
  change Eval Body (tryClauses (SpecTec.«$free_const_clauses» xs)) _ _ _
  apply tryClauses_cons_success
  unfold SpecTec.«$free_const:clause:0»
  apply Eval.bind_success (block_free_total xs n h)
  exact Eval.pure _

end properties.wasm_module_ok.ConstructiveFreeConstants
