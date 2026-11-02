import properties.wasm_module_ok.ConstructiveRefs
import properties.wasm_module_ok.FreeListValidation
import properties.wasm_module_not_ok.InitialContextValidation

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace properties.wasm_module_ok.ConstructiveFreeTypes
open SpecTec SpecTecExecution
open properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open FreeUnionValidation

/-- Pure structural syntax summaries. These never inspect validation results. -/
def listFree {α : Type} (f : α → free) : List α → free
  | [] => emptyFree
  | x :: xs => unionFree (f x) (listFree f xs)

theorem list_free_total {α : Type} (f : α → free) (call : α → SpecTecCall free)
    (xs : List α) (n : Nat)
    (h : ∀ x ∈ xs, Eval specTecProgram (.call ⟨free, call x⟩)
      n (.success (.of (f x))) n) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_list» α call xs⟩)
      n (.success (.of (listFree f xs))) n := by
  induction xs with
  | nil =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_list_clauses» α call []) ()) _ _ _
    apply firstSuccess_cons_success
    change Eval specTecProgram (SpecTec.«$free_list:clause:0» α call [])
      n (.success (.of emptyFree)) n
    unfold SpecTec.«$free_list:clause:0»
    apply Eval.bind_success (Eval.guard_true (by rfl))
    apply Eval.bind_success (free_empty_total n)
    exact Eval.pure _
  | cons x xs ih =>
    apply (FreeListValidation.free_list_cons_success_iff call x xs
      (listFree f (x :: xs)) n n).2
    exact ⟨f x, listFree f xs, n, n, h x (by simp),
      ih (by intro y hy; exact h y (by simp [hy])), fold_left_singleton_total _ _ n⟩

def typevarFree : typevar → free
  | .StatX x => {emptyFree with TYPES := .«`{ % `}» [x]}
  | .RecX _ => emptyFree

theorem update_types_total (xs : List Nat) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$update_types» (.«`{ % `}» xs)⟩)
      n (.success (.of {emptyFree with TYPES := .«`{ % `}» xs})) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$update_types_clauses» (.«`{ % `}» xs)) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$update_types:clause:0»
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

theorem typevar_free_total (tv : typevar) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_typevar» tv⟩)
      n (.success (.of (typevarFree tv))) n := by
  cases tv with
  | StatX x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_typevar_clauses» (.StatX x)) ()) _ _ _
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_typevar:clause:0»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
    apply Eval.bind_success (update_types_total [x] n)
    exact Eval.pure _
  | RecX x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_typevar_clauses» (.RecX x)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_typevar:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:typevar:StatX»]
    · apply firstSuccess_cons_success
      unfold SpecTec.«$free_typevar:clause:1»
      apply Eval.bind_success (Eval.guard_true rfl)
      apply Eval.bind_success (free_empty_total n)
      exact Eval.pure _

def heaptypeFree : heaptype → free
  | .VarHT tv => typevarFree tv
  | _ => emptyFree

theorem heaptype_free_total (ht : heaptype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_heaptype» ht⟩)
      n (.success (.of (heaptypeFree ht))) n := by
  cases ht <;> apply Eval.call
  all_goals change Eval specTecProgram (firstSuccess (SpecTec.«$free_heaptype_clauses» _) ()) _ _ _
  case VarHT tv =>
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_heaptype:clause:0»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (typevar_free_total tv n)
    exact Eval.pure _
  all_goals
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_heaptype:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«sub:heaptype:heaptypeVar»]
    · apply firstSuccess_cons_success
      unfold SpecTec.«$free_heaptype:clause:1»
      apply Eval.bind_success (free_empty_total n)
      exact Eval.pure _

def numtypeFree (x : numtype) : free :=
  match x with | _ => emptyFree

theorem numtype_free_total (x : numtype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_numtype» x⟩)
      n (.success (.of (numtypeFree x))) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_numtype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_numtype:clause:0»
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

def vectypeFree (x : vectype) : free :=
  match x with | _ => emptyFree

theorem vectype_free_total (x : vectype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_vectype» x⟩)
      n (.success (.of (vectypeFree x))) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_vectype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_vectype:clause:0»
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

def packtypeFree (x : packtype) : free :=
  match x with | _ => emptyFree

theorem packtype_free_total (x : packtype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_packtype» x⟩)
      n (.success (.of (packtypeFree x))) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_packtype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_packtype:clause:0»
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

def reftypeFree (x : reftype) : free :=
  match x with | .«% %» _ ht => heaptypeFree ht

theorem reftype_free_total (x : reftype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_reftype» x⟩)
      n (.success (.of (reftypeFree x))) n := by
  rcases x with ⟨nu, ht⟩
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_reftype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_reftype:clause:0»
  apply Eval.bind_success (heaptype_free_total ht n)
  exact Eval.pure _

def valtypeFree : valtype → free
  | .NumT nt => numtypeFree nt
  | .VecT vt => vectypeFree vt
  | .RefT rt => reftypeFree rt
  | .BotT  => emptyFree

theorem valtype_free_total (x : valtype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_valtype» x⟩)
      n (.success (.of (valtypeFree x))) n := by
  cases x with
  | NumT nt =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_valtype_clauses» (.NumT nt)) ()) _ _ _
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_valtype:clause:0»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (numtype_free_total nt n)
    exact Eval.pure _
  | VecT vt =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_valtype_clauses» (.VecT vt)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_valtype:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:valtype:NumT»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_valtype:clause:1»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (vectype_free_total vt n)
    exact Eval.pure _
  | RefT rt =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_valtype_clauses» (.RefT rt)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_valtype:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:valtype:NumT»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_valtype:clause:1»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:valtype:VecT»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_valtype:clause:2»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (reftype_free_total rt n)
    exact Eval.pure _
  | BotT  =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_valtype_clauses» (.BotT )) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_valtype:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:valtype:NumT»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_valtype:clause:1»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:valtype:VecT»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_valtype:clause:2»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:valtype:RefT»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_valtype:clause:3»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (free_empty_total n)
    exact Eval.pure _

def storagetypeFree : storagetype → free
  | .ValStorageT vt => valtypeFree vt
  | .PackStorageT pt => packtypeFree pt

theorem storagetype_free_total (x : storagetype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_storagetype» x⟩)
      n (.success (.of (storagetypeFree x))) n := by
  cases x with
  | ValStorageT vt =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_storagetype_clauses» (.ValStorageT vt)) ()) _ _ _
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_storagetype:clause:0»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (valtype_free_total vt n)
    exact Eval.pure _
  | PackStorageT pt =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_storagetype_clauses» (.PackStorageT pt)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_storagetype:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:storagetype:ValStorageT»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_storagetype:clause:1»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (packtype_free_total pt n)
    exact Eval.pure _

def fieldtypeFree (x : fieldtype) : free :=
  match x with | .FieldT _ st => storagetypeFree st

theorem fieldtype_free_total (x : fieldtype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_fieldtype» x⟩)
      n (.success (.of (fieldtypeFree x))) n := by
  rcases x with ⟨mu, st⟩
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_fieldtype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_fieldtype:clause:0»
  apply Eval.bind_success (storagetype_free_total st n)
  exact Eval.pure _

def structtypeFree (x : structtype) : free :=
  match x with | .StructT fs => listFree fieldtypeFree fs

theorem structtype_free_total (x : structtype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_structtype» x⟩)
      n (.success (.of (structtypeFree x))) n := by
  rcases x with ⟨fs⟩
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_structtype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_structtype:clause:0»
  apply Eval.bind_success (list_free_total fieldtypeFree SpecTecCall.«$free_fieldtype» fs n (fun x _ => fieldtype_free_total x n))
  exact Eval.pure _

def arraytypeFree (x : arraytype) : free :=
  match x with | .ArrayT f => fieldtypeFree f

theorem arraytype_free_total (x : arraytype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_arraytype» x⟩)
      n (.success (.of (arraytypeFree x))) n := by
  rcases x with ⟨f⟩
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_arraytype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_arraytype:clause:0»
  apply Eval.bind_success (fieldtype_free_total f n)
  exact Eval.pure _

def functypeFree (x : functype) : free :=
  match x with | .FuncT ins outs => unionFree (listFree valtypeFree ins) (listFree valtypeFree outs)

theorem functype_free_total (x : functype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_functype» x⟩)
      n (.success (.of (functypeFree x))) n := by
  rcases x with ⟨ins, outs⟩
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_functype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_functype:clause:0»
  apply Eval.bind_success (list_free_total valtypeFree SpecTecCall.«$free_valtype» ins n (fun x _ => valtype_free_total x n))
  apply Eval.bind_success (list_free_total valtypeFree SpecTecCall.«$free_valtype» outs n (fun x _ => valtype_free_total x n))
  apply Eval.bind_success (free_union_total _ _ n)
  exact Eval.pure _

def strtypeFree : strtype → free
  | .DefStructT st => structtypeFree st
  | .DefArrayT arr => arraytypeFree arr
  | .DefFuncT ft => functypeFree ft

theorem strtype_free_total (x : strtype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_strtype» x⟩)
      n (.success (.of (strtypeFree x))) n := by
  cases x with
  | DefStructT st =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_strtype_clauses» (.DefStructT st)) ()) _ _ _
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_strtype:clause:0»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (structtype_free_total st n)
    exact Eval.pure _
  | DefArrayT arr =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_strtype_clauses» (.DefArrayT arr)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_strtype:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:strtype:DefStructT»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_strtype:clause:1»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (arraytype_free_total arr n)
    exact Eval.pure _
  | DefFuncT ft =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_strtype_clauses» (.DefFuncT ft)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_strtype:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:strtype:DefStructT»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_strtype:clause:1»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:strtype:DefArrayT»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_strtype:clause:2»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (functype_free_total ft n)
    exact Eval.pure _

def subtypeFree (x : SpecTec.subtype) : free :=
  match x with | .SubT _ supers st => unionFree (listFree heaptypeFree supers) (strtypeFree st)

theorem subtype_free_total (x : SpecTec.subtype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_subtype» x⟩)
      n (.success (.of (subtypeFree x))) n := by
  rcases x with ⟨fin, supers, st⟩
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_subtype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_subtype:clause:0»
  apply Eval.bind_success (list_free_total heaptypeFree SpecTecCall.«$free_heaptype» supers n (fun x _ => heaptype_free_total x n))
  apply Eval.bind_success (strtype_free_total st n)
  apply Eval.bind_success (free_union_total _ _ n)
  exact Eval.pure _

def rectypeFree (x : rectype) : free :=
  match x with | .RecT sts => listFree subtypeFree sts

theorem rectype_free_total (x : rectype) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_rectype» x⟩)
      n (.success (.of (rectypeFree x))) n := by
  rcases x with ⟨sts⟩
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_rectype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_rectype:clause:0»
  apply Eval.bind_success (list_free_total subtypeFree SpecTecCall.«$free_subtype» sts n (fun x _ => subtype_free_total x n))
  exact Eval.pure _

def type_Free (x : SpecTec.type) : free :=
  match x with | x => rectypeFree x

theorem type_free_total (x : SpecTec.type) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_type_» x⟩)
      n (.success (.of (type_Free x))) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_type__clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_type_:clause:0»
  apply Eval.bind_success (rectype_free_total x n)
  exact Eval.pure _

end properties.wasm_module_ok.ConstructiveFreeTypes
