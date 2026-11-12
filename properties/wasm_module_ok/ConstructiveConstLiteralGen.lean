import properties.wasm_module_ok.ConstructiveConstBuilders
import properties.wasm_module_ok.ConstructiveGenAudit
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveConstLiteralGen
open SpecTec properties.wasm_module_ok ConstructiveConstTree ConstructiveGenAudit
open properties.wasm_module_ok.ConstructiveConstBuilders

def integers : Gen Int := Gen.pick (Int.ofNat <$> Gen.arbNat) (Int.negSucc <$> Gen.arbNat)
def magnitudes : Gen fmag := Gen.pick
  (do let m ← Gen.arbNat; let e ← integers; pure (.NORM m e))
  (Gen.pick (.SUBNORM <$> Gen.arbNat) (Gen.pick (pure .INF) (.NAN <$> Gen.arbNat)))
def floats32 : Gen f32 := Gen.pick (.POS <$> magnitudes) (.NEG <$> magnitudes)
def floats64 : Gen f64 := Gen.pick (.POS <$> magnitudes) (.NEG <$> magnitudes)

theorem integers_support (v : Int) : Gen.support integers v := by
  cases v <;> simp [integers]
theorem magnitudes_support (v : fmag) : Gen.support magnitudes v := by
  cases v <;> simp [magnitudes,integers_support]
theorem floats32_support (v : f32) : Gen.support floats32 v := by
  cases v <;> simp [floats32,magnitudes_support]
theorem floats64_support (v : f64) : Gen.support floats64 v := by
  cases v <;> simp [floats64,magnitudes_support]

theorem integers_audit : Structural integers := by simp [integers]
theorem magnitudes_audit : Structural magnitudes := by simp [magnitudes,integers_audit]
theorem floats32_audit : Structural floats32 := by simp [floats32,magnitudes_audit]
theorem floats64_audit : Structural floats64 := by simp [floats64,magnitudes_audit]

def numbers (c : context) : (t : numtype) → Gen (Typed c (.NumT t))
  | .I32T => (fun n => number c (.I32 n)) <$> Gen.arbNat
  | .I64T => (fun n => number c (.I64 n)) <$> Gen.arbNat
  | .F32T => (fun n => number c (.F32 n)) <$> floats32
  | .F64T => (fun n => number c (.F64 n)) <$> floats64

def vectors (c : context) : Gen (Typed c (.VecT .V128T)) :=
  (fun n => vector c (.V128 n)) <$> Gen.arbNat

theorem numbers_audit (c : context) (t : numtype) : Structural (numbers c t) := by
  cases t <;> simp [numbers,floats32_audit,floats64_audit]
theorem vectors_audit (c : context) : Structural (vectors c) := by simp [vectors]

theorem numbers_support (c : context) (v : num_) :
    Gen.support (numbers c (ConstLiteralEffect.numericType v)) (number c v) := by
  cases v <;> simp [ConstLiteralEffect.numericType,numbers,floats32_support,floats64_support] <;> exact ⟨_,rfl⟩
theorem vectors_support (c : context) (v : vec_) :
    Gen.support (vectors c) (vector c v) := by
  cases v <;> simp [vectors] <;> exact ⟨_,rfl⟩

#print axioms numbers_support
#print axioms numbers_audit
end properties.wasm_module_ok.ConstructiveConstLiteralGen
