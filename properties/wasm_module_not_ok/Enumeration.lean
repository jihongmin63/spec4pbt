import properties.wasm_module_not_ok.bundle.Helpers
import Mathlib.Tactic.DeriveEncodable
import Mathlib.Logic.Equiv.List

set_option autoImplicit false

/- Lawful encodings for the full Wasm instruction's nonrecursive opcode fields.
   Nested recursive syntax and type-family payloads remain separate obligations. -/

deriving instance Encodable for SpecTec.ftestop
deriving instance Encodable for SpecTec.packtype
deriving instance Encodable for SpecTec.extension
deriving instance Encodable for SpecTec.packshape
deriving instance Encodable for SpecTec.vextension

deriving instance Encodable for SpecTec.Inn
deriving instance Encodable for SpecTec.Fnn
deriving instance Encodable for SpecTec.Vnn
deriving instance Encodable for SpecTec.Cnn
deriving instance Encodable for SpecTec.Pnn
deriving instance Encodable for SpecTec.Jnn
deriving instance Encodable for SpecTec.Lnn

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
deriving instance Encodable for SpecTec.«catch»

section
variable [Encodable SpecTec.valtype]
deriving instance Encodable for SpecTec.blocktype
end

namespace properties.wasm_module_not_ok.Enumeration

theorem laneop_roundtrip {A B C D E F : Type}
    [Encodable A] [Encodable B] [Encodable C]
    [Encodable D] [Encodable E] [Encodable F]
    (x : SpecTec.laneop A B C D E F) :
    Encodable.decode (Encodable.encode x) = some x :=
  Encodable.encodek x

theorem vibinop_roundtrip (x : SpecTec.vibinop) :
    Encodable.decode (Encodable.encode x) = some x :=
  Encodable.encodek x

section
variable [Encodable SpecTec.valtype]
variable [Encodable SpecTec.numtype] [Encodable SpecTec.vectype]
variable [Encodable SpecTec.f32] [Encodable SpecTec.f64]

example : Encodable SpecTec.blocktype := inferInstance
example : Encodable SpecTec.num_ := inferInstance
example : Encodable SpecTec.unop_ := inferInstance
example : Encodable SpecTec.binop_ := inferInstance
example : Encodable SpecTec.relop_ := inferInstance
example : Encodable SpecTec.testop_ := inferInstance
example : Encodable SpecTec.cvtop_ := inferInstance
example : Encodable SpecTec.vtestop_ := inferInstance
example : Encodable SpecTec.vunop_ := inferInstance
example : Encodable SpecTec.vbinop_ := inferInstance
example : Encodable SpecTec.vternop_ := inferInstance
example : Encodable SpecTec.vrelop_ := inferInstance
example : Encodable SpecTec.vcvtop_ := inferInstance
example : Encodable SpecTec.vshiftop_ := inferInstance
example : Encodable SpecTec.vbitmaskop_ := inferInstance
example : Encodable SpecTec.vvtestop_ := inferInstance
example : Encodable SpecTec.vvunop_ := inferInstance
example : Encodable SpecTec.vvbinop_ := inferInstance
example : Encodable SpecTec.vvternop_ := inferInstance
example : Encodable SpecTec.vsplatop_ := inferInstance
example : Encodable SpecTec.vextractop_ := inferInstance
example : Encodable SpecTec.vreplaceop_ := inferInstance
example : Encodable SpecTec.loadop_ := inferInstance
example : Encodable SpecTec.storeop_ := inferInstance
example : Encodable SpecTec.vloadop_ := inferInstance
example : Encodable SpecTec.vstoreop_ := inferInstance
example : Encodable SpecTec.vlaneop_ := inferInstance

end

end properties.wasm_module_not_ok.Enumeration
