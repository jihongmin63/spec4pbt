import properties.wasm_module_ok.ConstructiveLists
import properties.wasm_module_ok.StrtypeValidation

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveTypeShapes
open SpecTec SpecTecExecution
open properties.wasm_module_ok

def storage (c : context) : Gen storagetype :=
  Gen.pick (storagetype.ValStorageT <$> ConstructiveTypeAtoms.valtypes c)
    (ConstructiveTypeAtoms.choose (.PackStorageT .I8) [.PackStorageT .I16])

@[simp] theorem storage_support (c : context) (s : storagetype) :
    Gen.support (storage c) s ↔ StoragetypeValidation.storagetypeValid c s = true := by
  cases s with
  | ValStorageT v => simp [storage, StoragetypeValidation.storagetypeValid]
  | PackStorageT p => cases p <;> simp [storage, StoragetypeValidation.storagetypeValid]

def fields (c : context) : Gen fieldtype := do
  let s ← storage c
  Gen.pick (pure (.FieldT .Cons s)) (pure (.FieldT .Var s))

@[simp] theorem fields_support (c : context) (f : fieldtype) :
    Gen.support (fields c) f ↔ FieldtypeValidation.fieldtypeValid c f = true := by
  cases f with
  | FieldT m s => cases m <;> simp [fields, FieldtypeValidation.fieldtypeValid]

@[simp] theorem all_fields (c : context) (fs : List fieldtype) :
    Gen.support (ConstructiveLists.all (fields c)) fs ↔
      StructtypeFieldListValidation.allFieldsValid c fs = true := by
  rw [ConstructiveLists.all_support]
  induction fs with
  | nil => simp [StructtypeFieldListValidation.allFieldsValid]
  | cons f fs ih => simp [StructtypeFieldListValidation.allFieldsValid, ← ih]

@[simp] theorem all_vals (c : context) (vs : List valtype) :
    Gen.support (ConstructiveLists.all (ConstructiveTypeAtoms.valtypes c)) vs ↔
      FunctypeValidation.resulttypeValid c vs = true := by
  rw [ConstructiveLists.all_support]
  change (∀ v ∈ vs, Gen.support (ConstructiveTypeAtoms.valtypes c) v) ↔
    ResulttypeListValidation.allValtypesValid c vs = true
  induction vs with
  | nil => simp [ResulttypeListValidation.allValtypesValid]
  | cons v vs ih => simp [ResulttypeListValidation.allValtypesValid, ← ih]

def structs (c : context) : Gen structtype :=
  structtype.StructT <$> ConstructiveLists.all (fields c)

def arrays (c : context) : Gen arraytype := arraytype.ArrayT <$> fields c

def functions (c : context) : Gen functype := do
  let ins ← ConstructiveLists.all (ConstructiveTypeAtoms.valtypes c)
  let outs ← ConstructiveLists.all (ConstructiveTypeAtoms.valtypes c)
  pure (.FuncT ins outs)

@[simp] theorem structs_support (c : context) (s : structtype) :
    Gen.support (structs c) s ↔ StructArrayValidation.structtypeValid c s = true := by
  cases s
  simp [structs, StructArrayValidation.structtypeValid, -ConstructiveLists.all_support]

@[simp] theorem arrays_support (c : context) (s : arraytype) :
    Gen.support (arrays c) s ↔ StructArrayValidation.arraytypeValid c s = true := by
  cases s
  simp [arrays, StructArrayValidation.arraytypeValid]

@[simp] theorem functions_support (c : context) (s : functype) :
    Gen.support (functions c) s ↔ FunctypeValidation.functypeValid c s = true := by
  cases s
  simp [functions, FunctypeValidation.functypeValid, -ConstructiveLists.all_support]

/-- All structural type shapes, with arbitrary finite fields/parameters/results.
This is the exact Strtype_ok domain. Declared-supertype variance is separate. -/
def shapes (c : context) : Gen strtype :=
  Gen.pick (strtype.DefStructT <$> structs c)
    (Gen.pick (strtype.DefArrayT <$> arrays c) (strtype.DefFuncT <$> functions c))

@[simp] theorem shapes_support (c : context) (s : strtype) :
    Gen.support (shapes c) s ↔ StrtypeValidation.strtypeValid c s = true := by
  cases s <;> simp [shapes, StrtypeValidation.strtypeValid]

theorem shapes_exact (c : context) (s : strtype) (start finish : Nat) :
    Eval Body (.call ⟨Unit, Call.Strtype_ok c s⟩)
      start (.success (.of ())) finish ↔
      Gen.support (shapes c) s ∧ finish = start := by
  rw [shapes_support, StrtypeValidation.strtype_success_iff_valid]

theorem storage_audit (c : context) : ConstructiveGenAudit.Structural (storage c) := by
  apply And.intro
  · rw [ConstructiveGenAudit.map_audit]
    exact ConstructiveGenAudit.finite_audit _ (ConstructiveTypeAtoms.valtypes_finite c)
  · exact ConstructiveGenAudit.finite_audit _ (ConstructiveTypeAtoms.finite_choose _ _)

theorem fields_audit (c : context) : ConstructiveGenAudit.Structural (fields c) :=
  ⟨storage_audit c, fun _ => ⟨trivial, trivial⟩⟩

theorem structs_audit (c : context) : ConstructiveGenAudit.Structural (structs c) := by
  rw [structs, ConstructiveGenAudit.map_audit]
  exact ConstructiveLists.all_audit _ (fields_audit c)

theorem arrays_audit (c : context) : ConstructiveGenAudit.Structural (arrays c) := by
  rw [arrays, ConstructiveGenAudit.map_audit]
  exact fields_audit c

theorem functions_audit (c : context) : ConstructiveGenAudit.Structural (functions c) := by
  have h := ConstructiveLists.all_audit _
    (ConstructiveGenAudit.finite_audit _ (ConstructiveTypeAtoms.valtypes_finite c))
  exact ⟨h, fun _ => ⟨h, fun _ => trivial⟩⟩

theorem shapes_audit (c : context) : ConstructiveGenAudit.Structural (shapes c) := by
  simp only [shapes, ConstructiveGenAudit.pick_audit, ConstructiveGenAudit.map_audit]
  exact ⟨structs_audit c, arrays_audit c, functions_audit c⟩

theorem shapes_total (c : context) : Gen.total (shapes c) :=
  ConstructiveGenAudit.audit_total _ (shapes_audit c)

end properties.wasm_module_ok.ConstructiveTypeShapes
