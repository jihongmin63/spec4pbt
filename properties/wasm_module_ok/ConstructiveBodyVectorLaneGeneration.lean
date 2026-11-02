import properties.wasm_module_ok.ConstructiveBodyVectorLaneCalls
import properties.wasm_module_ok.ConstructiveBodyOperatorProductions
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyVectorLaneGeneration
open SpecTec properties.wasm_module_ok ConstructiveConstTableCore
open ConstructiveBodyVectorLaneCalls ConstructiveBodyOperatorTypes ConstructiveBodyEnvironment ConstructiveBodyProductions

inductive Lane where
  | I8x16
  | I16x8
  | I32x4
  | I64x2
  | F32x4
  | F64x2
  deriving DecidableEq

def maximum : Lane → Nat
  | .I8x16 => 15
  | .I16x8 => 7
  | .I32x4 => 3
  | .I64x2 => 1
  | .F32x4 => 3
  | .F64x2 => 1

def scalar : Lane → numtype
  | .I8x16 => .I32T
  | .I16x8 => .I32T
  | .I32x4 => .I32T
  | .I64x2 => .I64T
  | .F32x4 => .F32T
  | .F64x2 => .F64T

def Suffix : Lane → Type
  | .I8x16 => extension
  | .I16x8 => extension
  | .I32x4 => void
  | .I64x2 => void
  | .F32x4 => void
  | .F64x2 => void

def suffixes : (l : Lane) → ConstructiveBodyOperatorEnums.Domain (Suffix l)
  | .I8x16 => ConstructiveBodyOperatorEnums.domain_extension
  | .I16x8 => ConstructiveBodyOperatorEnums.domain_extension
  | .I32x4 => ConstructiveBodyOperatorEnums.domain_void
  | .I64x2 => ConstructiveBodyOperatorEnums.domain_void
  | .F32x4 => ConstructiveBodyOperatorEnums.domain_void
  | .F64x2 => ConstructiveBodyOperatorEnums.domain_void

def makeExtract : (l : Lane) → Fin (maximum l+1) → Suffix l → vextractop_
  | .I8x16,i,x => .V128 (.I8x16 (.Extract (i.val,x)))
  | .I16x8,i,x => .V128 (.I16x8 (.Extract (i.val,x)))
  | .I32x4,i,x => .V128 (.I32x4 (.Extract (i.val,x)))
  | .I64x2,i,x => .V128 (.I64x2 (.Extract (i.val,x)))
  | .F32x4,i,x => .V128 (.F32x4 (.Extract (i.val,x)))
  | .F64x2,i,x => .V128 (.F64x2 (.Extract (i.val,x)))

def makeReplace : (l : Lane) → Fin (maximum l+1) → vreplaceop_
  | .I8x16,i => .V128 (.I8x16 (.Replace i.val))
  | .I16x8,i => .V128 (.I16x8 (.Replace i.val))
  | .I32x4,i => .V128 (.I32x4 (.Replace i.val))
  | .I64x2,i => .V128 (.I64x2 (.Replace i.val))
  | .F32x4,i => .V128 (.F32x4 (.Replace i.val))
  | .F64x2,i => .V128 (.F64x2 (.Replace i.val))

theorem extract_properties (l : Lane) (i : Fin (maximum l+1)) (x : Suffix l) :
    extractIndex (makeExtract l i x)<laneCount (makeExtract l i x) ∧
      vecLaneType (makeExtract l i x)=scalar l := by
  cases l <;> exact ⟨i.isLt,rfl⟩
theorem replace_properties (l : Lane) (i : Fin (maximum l+1)) :
    replaceIndex (makeReplace l i)<laneCount (makeReplace l i) ∧
      vecLaneType (makeReplace l i)=scalar l := by
  cases l <;> exact ⟨i.isLt,rfl⟩

def Extract (l : Lane) := {op : vextractop_ // extractIndex op<laneCount op ∧ vecLaneType op=scalar l}
def Replace (l : Lane) := {op : vreplaceop_ // replaceIndex op<laneCount op ∧ vecLaneType op=scalar l}

def extracts (l : Lane) : Audited (Extract l) :=
  (ConstructiveBodyChoice.index (maximum l)).bind fun i =>
    (ConstructiveBodyOperatorEnums.generate (suffixes l)).map fun x => ⟨makeExtract l i x,extract_properties l i x⟩
def replaces (l : Lane) : Audited (Replace l) :=
  (ConstructiveBodyChoice.index (maximum l)).map fun i => ⟨makeReplace l i,replace_properties l i⟩

theorem extract_made (l : Lane) (i : Fin (maximum l+1)) (x : Suffix l) :
    Gen.support (extracts l).generator ⟨makeExtract l i x,extract_properties l i x⟩ :=
  ⟨i,ConstructiveBodyChoice.index_support _ i,x,ConstructiveBodyOperatorEnums.generate_support _ x,rfl⟩
theorem replace_made (l : Lane) (i : Fin (maximum l+1)) :
    Gen.support (replaces l).generator ⟨makeReplace l i,replace_properties l i⟩ :=
  ⟨i,ConstructiveBodyChoice.index_support _ i,rfl⟩

theorem extract_inverse (op : vextractop_) (h : extractIndex op<laneCount op) :
    ∃l,∃i,∃x,makeExtract l i x =op := by
  cases op with | V128 v =>
   cases v with
   | I8x16 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      exact ⟨.I8x16,⟨i,h⟩,x,rfl⟩
   | I16x8 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      exact ⟨.I16x8,⟨i,h⟩,x,rfl⟩
   | I32x4 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      exact ⟨.I32x4,⟨i,h⟩,x,rfl⟩
   | I64x2 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      exact ⟨.I64x2,⟨i,h⟩,x,rfl⟩
   | F32x4 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      exact ⟨.F32x4,⟨i,h⟩,x,rfl⟩
   | F64x2 a =>
     cases a with | Extract a =>
      rcases a with ⟨i,x⟩
      exact ⟨.F64x2,⟨i,h⟩,x,rfl⟩

theorem extract_complete (op : vextractop_) (h : extractIndex op<laneCount op) :
    ∃l,∃v : Extract l,Gen.support (extracts l).generator v ∧ v.val=op := by
  obtain ⟨l,i,x,rfl⟩ := extract_inverse op h
  exact ⟨l,_,extract_made l i x,rfl⟩

theorem replace_inverse (op : vreplaceop_) (h : replaceIndex op<laneCount op) :
    ∃l,∃i,makeReplace l i =op := by
  cases op with | V128 v =>
   cases v with
   | I8x16 a =>
     cases a with | Replace a =>
      exact ⟨.I8x16,⟨a,h⟩,rfl⟩
   | I16x8 a =>
     cases a with | Replace a =>
      exact ⟨.I16x8,⟨a,h⟩,rfl⟩
   | I32x4 a =>
     cases a with | Replace a =>
      exact ⟨.I32x4,⟨a,h⟩,rfl⟩
   | I64x2 a =>
     cases a with | Replace a =>
      exact ⟨.I64x2,⟨a,h⟩,rfl⟩
   | F32x4 a =>
     cases a with | Replace a =>
      exact ⟨.F32x4,⟨a,h⟩,rfl⟩
   | F64x2 a =>
     cases a with | Replace a =>
      exact ⟨.F64x2,⟨a,h⟩,rfl⟩

theorem replace_complete (op : vreplaceop_) (h : replaceIndex op<laneCount op) :
    ∃l,∃v : Replace l,Gen.support (replaces l).generator v ∧ v.val=op := by
  obtain ⟨l,i,rfl⟩ := replace_inverse op h
  exact ⟨l,_,replace_made l i,rfl⟩

def extractProduction (c : context) (stack : inferresulttype) (env : Env c) (l : Lane) : Production c stack :=
  ConstructiveBodyOperatorProductions.production c stack env [.VecT .V128T] [.NumT (scalar l)]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> rfl)
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> rfl)
    (extracts l) (fun op => .«VEC.EXTRACT» op.val)
    (by intro op n; simpa only [op.property.2] using ConstructiveBodyVectorLaneCalls.extract c stack op.val n op.property.1)

def replaceProduction (c : context) (stack : inferresulttype) (env : Env c) (l : Lane) : Production c stack :=
  ConstructiveBodyOperatorProductions.production c stack env [.VecT .V128T,.NumT (scalar l)] [.VecT .V128T]
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl|rfl <;> rfl)
    (by intro t ht; simp only [List.mem_cons,List.not_mem_nil,or_false] at ht; rcases ht with rfl <;> rfl)
    (replaces l) (fun op => .«VEC.REPLACE» op.val)
    (by intro op n; simpa only [op.property.2] using ConstructiveBodyVectorLaneCalls.replace c stack op.val n op.property.1)

def lanes : List Lane := [.I8x16,.I16x8,.I32x4,.I64x2,.F32x4,.F64x2]
theorem mem_lanes (l : Lane) : l∈lanes := by cases l <;> decide

def all (c : context) (stack : inferresulttype) (env : Env c) : List (Production c stack) :=
  lanes.flatMap fun l => [extractProduction c stack env l,replaceProduction c stack env l]

#print axioms extract_complete
#print axioms replace_complete
end properties.wasm_module_ok.ConstructiveBodyVectorLaneGeneration
