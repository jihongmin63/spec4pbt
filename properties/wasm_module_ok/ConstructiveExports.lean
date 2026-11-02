import properties.wasm_module_ok.ConstructiveNames
import properties.wasm_module_ok.ExportsValidation

set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveExports
open SpecTec SpecTecExecution
open properties.wasm_module_ok

def descriptors (c : context) : List exportdesc :=
  (List.range c.FUNCS.length).map .FuncExport ++
  (List.range c.GLOBALS.length).map .GlobalExport ++
  (List.range c.TABLES.length).map .TableExport ++
  (List.range c.MEMS.length).map .MemExport ++
  (List.range c.TAGS.length).map .TagExport

def descriptorBound (c : context) : exportdesc → Prop
  | .FuncExport x => x < c.FUNCS.length
  | .GlobalExport x => x < c.GLOBALS.length
  | .TableExport x => x < c.TABLES.length
  | .MemExport x => x < c.MEMS.length
  | .TagExport x => x < c.TAGS.length

theorem mem_descriptors (c : context) (d : exportdesc) :
    d ∈ descriptors c ↔ descriptorBound c d := by
  cases d <;> simp [descriptors, descriptorBound]

def usedList : nameset → List name
  | .«`{ % `}» xs => xs

def Allowed (ds : List exportdesc) : nameset → List SpecTec.«export» → Prop
  | _, [] => True
  | used, e :: es => e.EDESC ∈ ds ∧ e.NAME ∉ usedList used ∧
      Allowed ds (ExportValidation.namesetAdd used e.NAME) es

theorem exportResult_shape (c : context) (used : nameset) (e : SpecTec.«export») :
    ExportValidation.exportResult c used e =
      if e.EDESC ∈ descriptors c ∧ e.NAME ∉ usedList used then
        some (ExportValidation.namesetAdd used e.NAME) else none := by
  cases used
  cases e with
  | mk name d =>
    cases d <;> simp [ExportValidation.exportResult, ExportValidation.exportTailResult,
      ExportSetValidation.inSetResult, mem_descriptors, descriptorBound, usedList]

theorem result_iff_allowed (c : context) (used : nameset) (es : List SpecTec.«export») :
    (∃ result, ExportsValidation.exportsResult c used es = some result) ↔
      Allowed (descriptors c) used es := by
  induction es generalizing used with
  | nil => simp [ExportsValidation.exportsResult, Allowed]
  | cons e es ih =>
    simp only [ExportsValidation.exportsResult, exportResult_shape]
    by_cases h : e.EDESC ∈ descriptors c ∧ e.NAME ∉ usedList used
    · simp [h, Allowed, ih]
    · simp only [if_neg h, Option.bind_none, reduceCtorEq, exists_false, false_iff, Allowed]
      rintro ⟨hd, hn, _⟩
      exact h ⟨hd, hn⟩

/-- A chosen positive count is inhabited because descriptor choice is nonempty
and finitely many used names always leave infinitely many fresh names. -/
def exactCount (head : exportdesc) (tail : List exportdesc) :
    Nat → nameset → Gen (List SpecTec.«export»)
  | 0, _ => pure []
  | n + 1, used => do
      let d ← ConstructiveTypeAtoms.choose head tail
      let name ← ConstructiveNames.fresh (usedList used)
      let es ← exactCount head tail n (ExportValidation.namesetAdd used name)
      pure (⟨name, d⟩ :: es)

theorem exactCount_support (head : exportdesc) (tail : List exportdesc)
    (n : Nat) (used : nameset) (es : List SpecTec.«export») :
    Gen.support (exactCount head tail n used) es ↔
      es.length = n ∧ Allowed (head :: tail) used es := by
  induction n generalizing used es with
  | zero => cases es <;> simp [exactCount, Allowed]
  | succ n ih =>
    cases es with
    | nil => simp [exactCount]
    | cons e es =>
      cases e with
      | mk name d =>
        simp [exactCount, ConstructiveNames.fresh_exact, ih, Allowed,
          and_assoc, and_left_comm, and_comm]

def exports (c : context) (used : nameset) : Gen (List SpecTec.«export») :=
  match descriptors c with
  | [] => pure []
  | d :: ds => do
      let n ← Gen.arbNat
      exactCount d ds n used

theorem exports_support (c : context) (used : nameset) (es : List SpecTec.«export») :
    Gen.support (exports c used) es ↔ Allowed (descriptors c) used es := by
  unfold exports
  cases hd : descriptors c with
  | nil => cases es <;> simp [Allowed]
  | cons d ds => simp [exactCount_support]

theorem exports_exact (c : context) (used : nameset) (es : List SpecTec.«export»)
    (n : Nat) : Gen.support (exports c used) es ↔
      ∃ result : nameset, Eval specTecProgram (.call ⟨nameset, SpecTecCall.Exports_ok c used es⟩)
        n (.success (.of result)) n := by
  rw [exports_support, ← result_iff_allowed]
  simp only [ExportsValidation.exports_success_iff_result, and_true]

theorem exactCount_audit (head : exportdesc) (tail : List exportdesc)
    (n : Nat) (used : nameset) :
    ConstructiveGenAudit.Structural (exactCount head tail n used) := by
  induction n generalizing used with
  | zero => trivial
  | succ n ih =>
    apply And.intro (ConstructiveGenAudit.finite_audit _
      (ConstructiveTypeAtoms.finite_choose head tail))
    intro d
    exact ⟨ConstructiveNames.fresh_audit _, fun name => ⟨ih _, fun _ => trivial⟩⟩

theorem exports_audit (c : context) (used : nameset) :
    ConstructiveGenAudit.Structural (exports c used) := by
  unfold exports
  cases descriptors c with
  | nil => trivial
  | cons d ds => exact ⟨ConstructiveGenAudit.arbNat_audit, fun n => exactCount_audit d ds n used⟩

theorem exports_total (c : context) (used : nameset) : Gen.total (exports c used) :=
  ConstructiveGenAudit.audit_total _ (exports_audit c used)


theorem exports_exact_supply (c : context) (used : nameset)
    (es : List SpecTec.«export») (n finish : Nat) :
    (∃ result : nameset, Eval specTecProgram
      (.call ⟨nameset, SpecTecCall.Exports_ok c used es⟩)
      n (.success (.of result)) finish) ↔
      Gen.support (exports c used) es ∧ finish = n := by
  simp only [ExportsValidation.exports_success_iff_result, exists_and_right]
  rw [result_iff_allowed, exports_support]

theorem empty_completion (c : context) (used : nameset) :
    Gen.support (exports c used) [] := by
  rw [exports_support]
  trivial

end properties.wasm_module_ok.ConstructiveExports
