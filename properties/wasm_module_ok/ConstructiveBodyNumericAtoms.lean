import properties.wasm_module_ok.ConstructiveBodySimpleAtoms
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyNumericAtoms
open SpecTec properties.wasm_module_ok ConstructiveBodyEnvironment ConstructiveBodyProductions ConstructiveConstTableCore

def payloads : (t : numtype) → Audited {v : num_ // ConstLiteralEffect.numericType v=t}
  | .I32T => (⟨Gen.arbNat,by simp⟩ : Audited Nat).map fun n => ⟨.I32 n,rfl⟩
  | .I64T => (⟨Gen.arbNat,by simp⟩ : Audited Nat).map fun n => ⟨.I64 n,rfl⟩
  | .F32T => (⟨ConstructiveConstLiteralGen.floats32,ConstructiveConstLiteralGen.floats32_audit⟩ : Audited f32).map fun f => ⟨.F32 f,rfl⟩
  | .F64T => (⟨ConstructiveConstLiteralGen.floats64,ConstructiveConstLiteralGen.floats64_audit⟩ : Audited f64).map fun f => ⟨.F64 f,rfl⟩

def numbers (c : context) (stack : inferresulttype) (env : Env c) (nt : numtype) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,[]) (.NoEllipses,[.NumT nt])
    (by simp [StackBacked])
    (by intro t ht; have he : t=.NumT nt := by simpa using ht
        subst t; intro heap hm; cases hm)
    ((payloads nt).map fun v => ⟨.CONST v.val,by
      intro n
      simpa only [←v.property] using ConstLiteralDispatch.const_dispatch_total c stack v.val n⟩)

def vectors (c : context) (stack : inferresulttype) (env : Env c) : Production c stack :=
  ConstructiveBodySimpleAtoms.unchanged c stack env (.NoEllipses,[]) (.NoEllipses,[.VecT .V128T])
    (by simp [StackBacked])
    (by intro t ht; have he : t=.VecT .V128T := by simpa using ht
        subst t; intro heap hm; cases hm)
    ((⟨Gen.arbNat,by simp⟩ : Audited Nat).map fun v =>
      ⟨.«VEC.CONST» (.V128 v),fun n => ConstVectorDispatch.vec_dispatch_total c stack (.V128 v) n⟩)

def literals (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  ([.I32T,.I64T,.F32T,.F64T].map (numbers c stack env)) ++ [vectors c stack env]

#print axioms numbers
end properties.wasm_module_ok.ConstructiveBodyNumericAtoms
