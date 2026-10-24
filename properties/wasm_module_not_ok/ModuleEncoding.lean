import properties.wasm_module_not_ok.InstructionCodec

set_option autoImplicit false

/- Base constructors and the full module envelope. The recursive value/type family is
   a separate obligation; the final module instance is conditional on that family. -/

instance : Encodable Char :=
  Encodable.ofLeftInverse Char.toNat Char.ofNat (fun c => Char.ofNat_toNat c)

instance : Encodable String :=
  Encodable.ofLeftInverse String.toList String.ofList
    (fun s => String.ofList_toList (s := s))

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

deriving instance Encodable for SpecTec.memtype
deriving instance Encodable for SpecTec.memory
deriving instance Encodable for SpecTec.tag
deriving instance Encodable for SpecTec.start
deriving instance Encodable for SpecTec.exportdesc
deriving instance Encodable for SpecTec.«export»

section
variable [Encodable SpecTec.heaptype] [Encodable SpecTec.reftype]
variable [Encodable SpecTec.valtype] [Encodable SpecTec.rectype]

deriving instance Encodable for SpecTec.globaltype
deriving instance Encodable for SpecTec.tabletype
deriving instance Encodable for SpecTec.«local»
deriving instance Encodable for SpecTec.global
deriving instance Encodable for SpecTec.table
deriving instance Encodable for SpecTec.func
deriving instance Encodable for SpecTec.active
deriving instance Encodable for SpecTec.elemmode
deriving instance Encodable for SpecTec.elem
deriving instance Encodable for SpecTec.datamode
deriving instance Encodable for SpecTec.data
deriving instance Encodable for SpecTec.importdesc
deriving instance Encodable for SpecTec.«import»
deriving instance Encodable for SpecTec.module

end

namespace properties.wasm_module_not_ok.ModuleEncoding

section
variable [Encodable SpecTec.heaptype] [Encodable SpecTec.reftype]
variable [Encodable SpecTec.valtype] [Encodable SpecTec.rectype]

theorem module_roundtrip (m : SpecTec.module) :
    Encodable.decode (Encodable.encode m) = some m := Encodable.encodek m

end

end properties.wasm_module_not_ok.ModuleEncoding
