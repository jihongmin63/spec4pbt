import properties.wasm_module_ok.ConstructiveFreeConstants
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace properties.wasm_module_ok.ConstructiveFreeModule
open SpecTec SpecTecExecution
open properties.wasm_module_ok
open properties.wasm_module_not_ok.Rejection
open FreeUnionValidation properties.wasm_module_ok.ConstructiveFreeTypes
open properties.wasm_module_ok.ConstructiveFreeInstructions properties.wasm_module_ok.ConstructiveFreeConstants

theorem update_tables_total (xs : List Nat) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$update_tables» (.«`{ % `}» xs)⟩)
      n (.success (.of {emptyFree with TABLES := .«`{ % `}» xs})) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$update_tables_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$update_tables:clause:0»
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

theorem update_mems_total (xs : List Nat) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$update_mems» (.«`{ % `}» xs)⟩)
      n (.success (.of {emptyFree with MEMS := .«`{ % `}» xs})) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$update_mems_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$update_mems:clause:0»
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

theorem update_tags_total (xs : List Nat) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$update_tags» (.«`{ % `}» xs)⟩)
      n (.success (.of {emptyFree with TAGS := .«`{ % `}» xs})) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$update_tags_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$update_tags:clause:0»
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

def globaltypeFree (x : globaltype) : free :=
  match x with | .GlobalT _ t => valtypeFree t

theorem globaltype_free_total (x : globaltype) (n : Nat)  :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_globaltype» x⟩)
      n (.success (.of (globaltypeFree x))) n := by
  rcases x with ⟨mu, t⟩
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_globaltype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_globaltype:clause:0»
  apply Eval.bind_success (valtype_free_total t n)
  exact Eval.pure _

def tabletypeFree (x : tabletype) : free :=
  match x with | .TableT _ _ rt => reftypeFree rt

theorem tabletype_free_total (x : tabletype) (n : Nat)  :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_tabletype» x⟩)
      n (.success (.of (tabletypeFree x))) n := by
  rcases x with ⟨at_, lim, rt⟩
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_tabletype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_tabletype:clause:0»
  apply Eval.bind_success (reftype_free_total rt n)
  exact Eval.pure _

def memtypeFree (_ : memtype) : free :=
  emptyFree

theorem memtype_free_total (x : memtype) (n : Nat)  :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_memtype» x⟩)
      n (.success (.of (memtypeFree x))) n := by
  cases x
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_memtype_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_memtype:clause:0»
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

def memFree (x : memory) : free :=
  memtypeFree x.MTYPE

theorem mem_free_total (x : memory) (n : Nat)  :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_mem» x⟩)
      n (.success (.of (memFree x))) n := by
  rcases x with ⟨mt⟩
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_mem_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_mem:clause:0»
  apply Eval.bind_success (memtype_free_total mt n)
  exact Eval.pure _

def globalFree (x : SpecTec.global) : free :=
  unionFree (globaltypeFree x.GTYPE) (constFree x.GINIT)

theorem global_free_total (x : SpecTec.global) (n : Nat) (h : ∀ i ∈ x.GINIT, Flat i) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_global» x⟩)
      n (.success (.of (globalFree x))) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_global_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_global:clause:0»
  apply Eval.bind_success (globaltype_free_total x.GTYPE n)
  apply Eval.bind_success (const_free_total x.GINIT n h)
  apply Eval.bind_success (free_union_total _ _ n)
  exact Eval.pure _

def tableFree (x : SpecTec.table) : free :=
  unionFree (tabletypeFree x.TTYPE) (constFree x.TINIT)

theorem table_free_total (x : SpecTec.table) (n : Nat) (h : ∀ i ∈ x.TINIT, Flat i) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_table» x⟩)
      n (.success (.of (tableFree x))) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_table_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_table:clause:0»
  apply Eval.bind_success (tabletype_free_total x.TTYPE n)
  apply Eval.bind_success (const_free_total x.TINIT n h)
  apply Eval.bind_success (free_union_total _ _ n)
  exact Eval.pure _

def importdescFree : importdesc → free
  | .FuncImport x => {emptyFree with TYPES := .«`{ % `}» [x]}
  | .TableImport x => tabletypeFree x
  | .MemImport x => memtypeFree x
  | .GlobalImport x => globaltypeFree x
  | .TagImport x => {emptyFree with TAGS := .«`{ % `}» [x]}

theorem importdesc_free_total (x : importdesc) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_importdesc» x⟩)
      n (.success (.of (importdescFree x))) n := by
  cases x with
  | FuncImport x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_importdesc_clauses» (.FuncImport x)) ()) _ _ _
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_importdesc:clause:0»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
    apply Eval.bind_success (update_types_total [x] n)
    exact Eval.pure _
  | TableImport x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_importdesc_clauses» (.TableImport x)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_importdesc:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:importdesc:FuncImport»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_importdesc:clause:1»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (tabletype_free_total x n)
    exact Eval.pure _
  | MemImport x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_importdesc_clauses» (.MemImport x)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_importdesc:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:importdesc:FuncImport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_importdesc:clause:1»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:importdesc:TableImport»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_importdesc:clause:2»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (memtype_free_total x n)
    exact Eval.pure _
  | GlobalImport x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_importdesc_clauses» (.GlobalImport x)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_importdesc:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:importdesc:FuncImport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_importdesc:clause:1»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:importdesc:TableImport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_importdesc:clause:2»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:importdesc:MemImport»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_importdesc:clause:3»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (globaltype_free_total x n)
    exact Eval.pure _
  | TagImport x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_importdesc_clauses» (.TagImport x)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_importdesc:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:importdesc:FuncImport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_importdesc:clause:1»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:importdesc:TableImport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_importdesc:clause:2»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:importdesc:MemImport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_importdesc:clause:3»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:importdesc:GlobalImport»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_importdesc:clause:4»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
    apply Eval.bind_success (update_tags_total [x] n)
    exact Eval.pure _

def exportdescFree : exportdesc → free
  | .FuncExport x => {emptyFree with FUNCS := .«`{ % `}» [x]}
  | .TableExport x => {emptyFree with TABLES := .«`{ % `}» [x]}
  | .MemExport x => {emptyFree with MEMS := .«`{ % `}» [x]}
  | .GlobalExport x => {emptyFree with GLOBALS := .«`{ % `}» [x]}
  | .TagExport x => {emptyFree with TAGS := .«`{ % `}» [x]}

theorem exportdesc_free_total (x : exportdesc) (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_exportdesc» x⟩)
      n (.success (.of (exportdescFree x))) n := by
  cases x with
  | FuncExport x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_exportdesc_clauses» (.FuncExport x)) ()) _ _ _
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_exportdesc:clause:0»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
    apply Eval.bind_success (FreeRefsValidation.update_funcs_total [x] n)
    exact Eval.pure _
  | TableExport x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_exportdesc_clauses» (.TableExport x)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_exportdesc:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:exportdesc:FuncExport»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_exportdesc:clause:1»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
    apply Eval.bind_success (update_tables_total [x] n)
    exact Eval.pure _
  | MemExport x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_exportdesc_clauses» (.MemExport x)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_exportdesc:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:exportdesc:FuncExport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_exportdesc:clause:1»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:exportdesc:TableExport»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_exportdesc:clause:2»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
    apply Eval.bind_success (update_mems_total [x] n)
    exact Eval.pure _
  | GlobalExport x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_exportdesc_clauses» (.GlobalExport x)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_exportdesc:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:exportdesc:FuncExport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_exportdesc:clause:1»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:exportdesc:TableExport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_exportdesc:clause:2»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:exportdesc:MemExport»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_exportdesc:clause:3»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
    apply Eval.bind_success (update_globals_total [x] n)
    exact Eval.pure _
  | TagExport x =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess (SpecTec.«$free_exportdesc_clauses» (.TagExport x)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_exportdesc:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:exportdesc:FuncExport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_exportdesc:clause:1»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:exportdesc:TableExport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_exportdesc:clause:2»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:exportdesc:MemExport»]
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_exportdesc:clause:3»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp [SpecTec.«exec:match:exportdesc:GlobalExport»]
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_exportdesc:clause:4»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (FreeRefsValidation.free_idx_total x n)
    apply Eval.bind_success (update_tags_total [x] n)
    exact Eval.pure _

def importFree (x : SpecTec.«import») : free :=
  importdescFree x.IDESC

theorem import_free_total (x : SpecTec.«import») (n : Nat)  :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_import» x⟩)
      n (.success (.of (importFree x))) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_import_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_import:clause:0»
  apply Eval.bind_success (importdesc_free_total x.IDESC n)
  exact Eval.pure _

def exportFree (x : SpecTec.«export») : free :=
  exportdescFree x.EDESC

theorem export_free_total (x : SpecTec.«export») (n : Nat)  :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_export» x⟩)
      n (.success (.of (exportFree x))) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_export_clauses» _) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_export:clause:0»
  apply Eval.bind_success (exportdesc_free_total x.EDESC n)
  exact Eval.pure _

def elemmodeFlat (m : elemmode) : Prop :=
  match m with
  | .Active a => ∀ i ∈ a.OFFSET, Flat i
  | _ => True

def elemmodeFree (m : elemmode) : free :=
  match m with
  | .Active a => unionFree {emptyFree with TABLES := .«`{ % `}» [a.INDEX]} (constFree a.OFFSET)
  | _ => emptyFree

theorem elemmode_free_total (m : elemmode) (n : Nat) (h : elemmodeFlat m) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_elemmode» SpecTecCall.«$update_tables» m⟩)
      n (.success (.of (elemmodeFree m))) n := by
  cases m with
  | Passive =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess
      (SpecTec.«$free_elemmode_clauses» SpecTecCall.«$update_tables» .Passive) ()) _ _ _
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_elemmode:clause:0»
    apply Eval.bind_success (Eval.guard_true (Or.inl rfl))
    apply Eval.bind_success (free_empty_total n)
    exact Eval.pure _
  | Declarative =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess
      (SpecTec.«$free_elemmode_clauses» SpecTecCall.«$update_tables» .Declarative) ()) _ _ _
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_elemmode:clause:0»
    apply Eval.bind_success (Eval.guard_true (Or.inr rfl))
    apply Eval.bind_success (free_empty_total n)
    exact Eval.pure _
  | Active a =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess
      (SpecTec.«$free_elemmode_clauses» SpecTecCall.«$update_tables» (.Active a)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_elemmode:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_elemmode:clause:1»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (update_tables_total [a.INDEX] n)
    apply Eval.bind_success (const_free_total a.OFFSET n h)
    apply Eval.bind_success (free_union_total _ _ n)
    exact Eval.pure _

def datamodeFlat (m : datamode) : Prop :=
  match m with
  | .Active a => ∀ i ∈ a.OFFSET, Flat i
  | _ => True

def datamodeFree (m : datamode) : free :=
  match m with
  | .Active a => unionFree {emptyFree with MEMS := .«`{ % `}» [a.INDEX]} (constFree a.OFFSET)
  | _ => emptyFree

theorem datamode_free_total (m : datamode) (n : Nat) (h : datamodeFlat m) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_datamode» SpecTecCall.«$update_mems» m⟩)
      n (.success (.of (datamodeFree m))) n := by
  cases m with
  | Passive =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess
      (SpecTec.«$free_datamode_clauses» SpecTecCall.«$update_mems» .Passive) ()) _ _ _
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_datamode:clause:0»
    apply Eval.bind_success (Eval.guard_true (rfl))
    apply Eval.bind_success (free_empty_total n)
    exact Eval.pure _
  | Active a =>
    apply Eval.call
    change Eval specTecProgram (firstSuccess
      (SpecTec.«$free_datamode_clauses» SpecTecCall.«$update_mems» (.Active a)) ()) _ _ _
    apply firstSuccess_cons_unmatch
    · unfold SpecTec.«$free_datamode:clause:0»
      apply Eval.bind_unmatch
      apply Eval.guard_false
      simp
    apply firstSuccess_cons_success
    unfold SpecTec.«$free_datamode:clause:1»
    apply Eval.bind_success (Eval.guard_true rfl)
    apply Eval.bind_success (update_mems_total [a.INDEX] n)
    apply Eval.bind_success (const_free_total a.OFFSET n h)
    apply Eval.bind_success (free_union_total _ _ n)
    exact Eval.pure _

def elemFree (e : elem) : free :=
  unionFree (listFree constFree e.EINIT) (elemmodeFree e.EMODE)

def dataFree (d : SpecTec.data) : free := datamodeFree d.DMODE

theorem elem_free_total (e : elem) (n : Nat)
    (hi : ∀ xs ∈ e.EINIT, ∀ i ∈ xs, Flat i) (hm : elemmodeFlat e.EMODE) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_elem» e⟩)
      n (.success (.of (elemFree e))) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_elem_clauses» e) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_elem:clause:0»
  apply Eval.bind_success (list_free_total constFree SpecTecCall.«$free_const» e.EINIT n
    (fun xs hx => const_free_total xs n (hi xs hx)))
  apply Eval.bind_success (elemmode_free_total e.EMODE n hm)
  apply Eval.bind_success (free_union_total _ _ n)
  exact Eval.pure _

theorem data_free_total (d : SpecTec.data) (n : Nat) (h : datamodeFlat d.DMODE) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_data» d⟩)
      n (.success (.of (dataFree d))) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_data_clauses» d) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_data:clause:0»
  apply Eval.bind_success (datamode_free_total d.DMODE n h)
  exact Eval.pure _

def PreludeFlat (m : SpecTec.module) : Prop :=
  ∀ xs, ConstructiveRefs.InitializerSite m xs → ∀ i ∈ xs, Flat i

/-- Exact full free record used by Module_ok, with its original field order.
Functions and START are excluded by the original Module_ok call itself. -/
def moduleFree (m : SpecTec.module) : free := unionsFree [
  listFree type_Free m.TYPES,
  listFree globalFree m.GLOBALS,
  listFree tableFree m.TABLES,
  listFree memFree m.MEMS,
  emptyFree,
  listFree elemFree m.ELEMS,
  listFree dataFree m.DATAS,
  listFree importFree m.IMPORTS,
  listFree exportFree m.EXPORTS]

theorem start_none_free_total (n : Nat) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_opt» SpecTec.start
      SpecTecCall.«$free_start» none⟩) n (.success (.of emptyFree)) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_opt_clauses» SpecTec.start
    SpecTecCall.«$free_start» none) ()) _ _ _
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_opt:clause:0»
  apply Eval.bind_success (Eval.guard_true rfl)
  apply Eval.bind_success (free_empty_total n)
  exact Eval.pure _

theorem module_free_total (m : SpecTec.module) (n : Nat) (h : PreludeFlat m) :
    Eval specTecProgram (.call ⟨free, SpecTecCall.«$free_module»
      ({{m with FUNCS := []} with START := none})⟩)
      n (.success (.of (moduleFree m))) n := by
  apply Eval.call
  change Eval specTecProgram (firstSuccess (SpecTec.«$free_module_clauses» _) ()) _ _ _
  unfold SpecTec.«$free_module_clauses»
  apply firstSuccess_cons_success
  unfold SpecTec.«$free_module:clause:0»
  apply Eval.bind_success (list_free_total type_Free SpecTecCall.«$free_type_» m.TYPES n
    (fun t _ => type_free_total t n))
  apply Eval.bind_success (list_free_total globalFree SpecTecCall.«$free_global» m.GLOBALS n
    (fun g hg => global_free_total g n (h _ (.global g hg))))
  apply Eval.bind_success (list_free_total tableFree SpecTecCall.«$free_table» m.TABLES n
    (fun t ht => table_free_total t n (h _ (.table t ht))))
  apply Eval.bind_success (list_free_total memFree SpecTecCall.«$free_mem» m.MEMS n
    (fun mt _ => mem_free_total mt n))
  apply Eval.bind_success (start_none_free_total n)
  apply Eval.bind_success (list_free_total elemFree SpecTecCall.«$free_elem» m.ELEMS n (by
    intro e he
    apply elem_free_total e n
    · intro xs hx
      exact h _ (.elemInit e xs he hx)
    · cases hm : e.EMODE <;> simp only [elemmodeFlat]
      rename_i a
      exact h _ (.elemOffset e a he hm)))
  apply Eval.bind_success (list_free_total dataFree SpecTecCall.«$free_data» m.DATAS n (by
    intro d hd
    apply data_free_total d n
    cases hm : d.DMODE <;> simp only [datamodeFlat]
    rename_i a
    exact h _ (.dataOffset d a hd hm)))
  apply Eval.bind_success (list_free_total importFree SpecTecCall.«$free_import» m.IMPORTS n
    (fun i _ => import_free_total i n))
  apply Eval.bind_success (list_free_total exportFree SpecTecCall.«$free_export» m.EXPORTS n
    (fun e _ => export_free_total e n))
  apply Eval.bind_success (free_unions_total _ n)
  exact Eval.pure _

/-- The computed record discharges the previous deferred-REFS premise. -/
theorem initializer_computed_refs (m : SpecTec.module) (hflat : PreludeFlat m)
    (c : context) (t : valtype) (xs : SpecTec.const)
    (hsite : ConstructiveRefs.InitializerSite m xs) (start finish : Nat)
    (h : Eval specTecProgram (.call ⟨Unit, SpecTecCall.Const_ok c t xs⟩)
      start (.success (.of ())) finish) :
    Eval specTecProgram (.call ⟨Unit, SpecTecCall.Const_ok {c with REFS := moduleFree m} t xs⟩)
      start (.success (.of ())) finish :=
  ConstructiveRefs.initializer_final_refs m (moduleFree m) 0
    (module_free_total m 0 hflat) c t xs hsite start finish h

end properties.wasm_module_ok.ConstructiveFreeModule
