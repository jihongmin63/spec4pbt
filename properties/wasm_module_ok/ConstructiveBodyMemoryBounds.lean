import properties.wasm_module_ok.ConstructiveBodyScalarSizes
import properties.wasm_module_ok.ConstructiveLimits
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMemoryBounds
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore

def packLog : packtype → Nat
  | .I8 => 0 | .I16 => 1 | .I32 => 2 | .I64 => 3
def numLog : numtype → Nat
  | .I32T | .F32T => 2 | .I64T | .F64T => 3

theorem pack_pow (pt : packtype) : ConstructiveBodyScalarSizes.packSize pt = Int.ofNat (2^packLog pt) := by cases pt <;> rfl
theorem num_pow (nt : numtype) : ConstructiveBodyScalarSizes.numSize nt = Int.ofNat (2^numLog nt) := by cases nt <;> rfl

theorem alignment (a k : Nat) (hk : k<4096) :
    (SpecTec.«$lsl_» (Int.ofNat 1) (Int.ofNat a) ≥ Int.ofNat 1 ∧
     SpecTec.«$lsl_» (Int.ofNat 1) (Int.ofNat a) ≤ Int.ofNat (2^k)) ↔ a≤k := by
  have he : SpecTec.«$lsl_» (Int.ofNat 1) (Int.ofNat a)=Int.ofNat (2^(min a 4096)) := by
    simp only [SpecTec.«$lsl_»,Int.toNat_natCast]
    change Int.ofNat (1 <<< min a 4096)=_
    rw [Nat.one_shiftLeft]
  rw [he]
  constructor
  · rintro ⟨_,h⟩
    have hb : 2^(min a 4096)≤2^k := Int.ofNat_le.mp h
    have hm := (Nat.pow_le_pow_iff_right (by decide : 1<2)).1 hb
    omega
  · intro h
    have hm : min a 4096=a := Nat.min_eq_left (by omega)
    rw [hm]
    exact ⟨Int.ofNat_le.mpr (Nat.one_le_pow a 2 (by decide)),
      Int.ofNat_le.mpr (Nat.pow_le_pow_of_le (by decide) h)⟩

/-- All and only lane immediates below the positive lane count, including every
negative integer. A natural slack constructs the integer directly. -/
def lane (bound : Nat) (positive : 0<bound) : Audited {i : Int // i<Int.ofNat bound} :=
  ⟨(fun (slack : Nat) => ⟨Int.ofNat bound-1-Int.ofNat slack,by change (bound : Int)-1-(slack : Int)<(bound : Int); omega⟩) <$> Gen.arbNat,
    by simpa using ConstructiveGenAudit.arbNat_audit⟩

theorem lane_complete (bound : Nat) (positive : 0<bound) (i : {i : Int // i<Int.ofNat bound}) :
    Gen.support (lane bound positive).generator i := by
  simp only [lane,Gen.Support.support_map,Gen.support_arbNat,true_and]
  refine ⟨(Int.ofNat bound-1-i.val).toNat,?_⟩
  apply Subtype.ext
  have hp := i.property
  have he : Int.ofNat ((Int.ofNat bound-1-i.val).toNat)=Int.ofNat bound-1-i.val := Int.toNat_of_nonneg (by omega)
  change i.val = Int.ofNat bound-1-Int.ofNat ((Int.ofNat bound-1-i.val).toNat)
  rw [he]
  omega

#print axioms alignment
#print axioms lane_complete
end properties.wasm_module_ok.ConstructiveBodyMemoryBounds
