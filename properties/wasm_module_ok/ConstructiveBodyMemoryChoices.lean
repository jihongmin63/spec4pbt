import properties.wasm_module_ok.ConstructiveBodyMemoryOperands
import properties.wasm_module_ok.ConstructiveBodyOperatorEnums
set_option autoImplicit false
namespace properties.wasm_module_ok.ConstructiveBodyMemoryChoices
open SpecTec properties.wasm_module_ok ConstructiveBodyMemoryBounds ConstructiveBodyMemoryOperands ConstructiveBodyScalarSizes ConstructiveConstTableCore

def offsets : (addr : addrtype) → Audited {offset : Nat // OffsetBound addr offset}
  | .I32AT => (ConstructiveBodyChoice.index 4294967295).map fun x => ⟨x.val,x.isLt⟩
  | .I64AT => (⟨Gen.arbNat,by simp⟩ : Audited Nat).map fun x => ⟨x,trivial⟩

theorem offsets_complete (addr : addrtype) (off : {offset : Nat // OffsetBound addr offset}) :
    Gen.support (offsets addr).generator off := by
  cases addr with
  | I32AT =>
    refine ⟨⟨off.val,off.property⟩,ConstructiveBodyChoice.index_support _ _,?_⟩
    rfl
  | I64AT =>
    refine ⟨off.val,by simp,?_⟩
    rfl

abbrev Pack (ty : numtype) := {pt : packtype // packSize pt<Int.ofNat (2^numLog ty)}

def packs : (ty : numtype) → List (Pack ty)
  | .I32T | .F32T => [⟨.I8,by decide⟩,⟨.I16,by decide⟩]
  | .I64T | .F64T => [⟨.I8,by decide⟩,⟨.I16,by decide⟩,⟨.I32,by decide⟩]

theorem packs_complete (ty : numtype) (pt : Pack ty) : pt∈packs ty := by
  rcases pt with ⟨pt,hp⟩
  cases ty <;> cases pt <;> simp [packs,packSize,numLog] at hp ⊢

def vextensions : ConstructiveBodyOperatorEnums.Domain vextension :=
  ⟨.ExtSplat,[.ExtZero,.ExtLane .Pack8x8 .SX,.ExtLane .Pack8x8 .ZX,
    .ExtLane .Pack16x4 .SX,.ExtLane .Pack16x4 .ZX,.ExtLane .Pack32x2 .SX,.ExtLane .Pack32x2 .ZX],by
    intro x; cases x with
    | ExtSplat => simp
    | ExtZero => simp
    | ExtLane shape ext => cases shape <;> cases ext <;> simp⟩

def numtypes : List numtype := [.I32T,.I64T,.F32T,.F64T]
theorem numtypes_complete (t : numtype) : t∈numtypes := by cases t <;> simp [numtypes]

structure Head (c : context) where
  addr : addrtype
  lim : limits
  lookup : c.MEMS[0]?=some (.MemoryT addr lim)

def head (c : context) : Option (Head c) :=
  match hx : (c.MEMS[0]? : Option memtype) with
  | none => none
  | some (memtype.MemoryT addr lim) => some ⟨addr,lim,hx⟩

theorem head_complete (c : context) (hd : Head c) : head c=some hd := by
  unfold head
  split
  next hx => rw [hd.lookup] at hx; cases hx
  next addr lim hx =>
    have he := hx.symm.trans hd.lookup
    have he : addr=hd.addr ∧ lim=hd.lim := by simpa using he
    rcases he with ⟨rfl,rfl⟩
    rfl

#print axioms packs_complete
#print axioms offsets_complete
end properties.wasm_module_ok.ConstructiveBodyMemoryChoices
