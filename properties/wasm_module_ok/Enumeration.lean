import properties.wasm_module_ok.bundle.Helpers
import Mathlib.Tactic.DeriveEncodable
import Mathlib.Logic.Equiv.List

set_option autoImplicit false

-- Constructive encodings for the nonrecursive leaves of the full Wasm AST.
-- Recursive type and instruction families are separate outstanding obligations.
deriving instance Encodable for SpecTec.set
deriving instance Encodable for SpecTec.fmag
deriving instance Encodable for SpecTec.f32
deriving instance Encodable for SpecTec.f64
deriving instance Encodable for SpecTec.externidx
deriving instance Encodable for SpecTec.null
deriving instance Encodable for SpecTec.«mut»
deriving instance Encodable for SpecTec.init
deriving instance Encodable for SpecTec.final
deriving instance Encodable for SpecTec.limits
deriving instance Encodable for SpecTec.typevar
deriving instance Encodable for SpecTec.typevarConcrete
deriving instance Encodable for SpecTec.addrtype
deriving instance Encodable for SpecTec.numtype
deriving instance Encodable for SpecTec.vectype
deriving instance Encodable for SpecTec.heaptypeVar
deriving instance Encodable for SpecTec.heaptypeConcrete
deriving instance Encodable for SpecTec.packtype
deriving instance Encodable for SpecTec.ftestop
deriving instance Encodable for SpecTec.extension
deriving instance Encodable for SpecTec.packshape
deriving instance Encodable for SpecTec.vextension
deriving instance Encodable for SpecTec.vecop
deriving instance Encodable for SpecTec.laneop
deriving instance Encodable for SpecTec.op
deriving instance Encodable for SpecTec.memop
deriving instance Encodable for SpecTec.iunop
deriving instance Encodable for SpecTec.funop
deriving instance Encodable for SpecTec.ibinop
deriving instance Encodable for SpecTec.fbinop
deriving instance Encodable for SpecTec.irelop
deriving instance Encodable for SpecTec.frelop
deriving instance Encodable for SpecTec.itestop
deriving instance Encodable for SpecTec.icvtop
deriving instance Encodable for SpecTec.fcvtop
deriving instance Encodable for SpecTec.void
deriving instance Encodable for SpecTec.vitestop
deriving instance Encodable for SpecTec.viunop
deriving instance Encodable for SpecTec.vfunop
deriving instance Encodable for SpecTec.vibinop
deriving instance Encodable for SpecTec.vfbinop
deriving instance Encodable for SpecTec.viternop
deriving instance Encodable for SpecTec.vfternop
deriving instance Encodable for SpecTec.virelop
deriving instance Encodable for SpecTec.vfrelop
deriving instance Encodable for SpecTec.vicvtop
deriving instance Encodable for SpecTec.vfcvtop
deriving instance Encodable for SpecTec.vishiftop
deriving instance Encodable for SpecTec.vibitmaskop
deriving instance Encodable for SpecTec.vvtestop
deriving instance Encodable for SpecTec.vvunop
deriving instance Encodable for SpecTec.vvbinop
deriving instance Encodable for SpecTec.vvternop
deriving instance Encodable for SpecTec.vnsplatop
deriving instance Encodable for SpecTec.vnextractop
deriving instance Encodable for SpecTec.vnreplaceop
deriving instance Encodable for SpecTec.externop_
deriving instance Encodable for SpecTec.initop_
deriving instance Encodable for SpecTec.memtype
deriving instance Encodable for SpecTec.memory
deriving instance Encodable for SpecTec.tag
deriving instance Encodable for SpecTec.start
deriving instance Encodable for SpecTec.exportdesc
deriving instance Encodable for SpecTec.«export»
deriving instance Encodable for SpecTec.«catch»

namespace properties.wasm_module_ok.Enumeration

def decodeCandidates {α : Type} [Encodable α] (n : Nat) : List α :=
  (List.range (n + 1)).filterMap (Encodable.decode (α := α))

theorem decodeCandidates_mono {α : Type} [Encodable α]
    (n k : Nat) (a : α) :
    a ∈ decodeCandidates n → a ∈ decodeCandidates (n + k) := by
  simp only [decodeCandidates, List.mem_filterMap, List.mem_range]
  rintro ⟨code, hcode, hdecode⟩
  exact ⟨code, by omega, hdecode⟩

theorem decodeCandidates_complete {α : Type} [Encodable α]
    (a : α) : ∃ n : Nat, a ∈ decodeCandidates n := by
  refine ⟨Encodable.encode a, ?_⟩
  simp only [decodeCandidates, List.mem_filterMap, List.mem_range]
  exact ⟨Encodable.encode a, Nat.lt_succ_self _, Encodable.encodek a⟩

theorem fmag_roundtrip (x : SpecTec.fmag) :
    Encodable.decode (Encodable.encode x) = some x :=
  Encodable.encodek x

theorem set_roundtrip {α : Type} [Encodable α] (x : SpecTec.set α) :
    Encodable.decode (Encodable.encode x) = some x :=
  Encodable.encodek x

theorem vecop_roundtrip {α : Type} [Encodable α] (x : SpecTec.vecop α) :
    Encodable.decode (Encodable.encode x) = some x :=
  Encodable.encodek x

theorem export_roundtrip (x : SpecTec.«export») :
    Encodable.decode (Encodable.encode x) = some x :=
  Encodable.encodek x

end properties.wasm_module_ok.Enumeration
