import properties.wasm_module_not_ok.InstructionEncoding

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace properties.wasm_module_not_ok.InstructionCodec

open properties.wasm_module_not_ok.InstructionEncoding

section
variable [Encodable SpecTec.valtype] [Encodable SpecTec.reftype]
variable [Encodable SpecTec.heaptype] [Encodable SpecTec.numtype]
variable [Encodable SpecTec.vectype] [Encodable SpecTec.f32] [Encodable SpecTec.f64]

mutual

def encodeInstruction : SpecTec.instr → Nat
  | .UNREACHABLE => Nat.pair 0 (0) + 1
  | .NOP => Nat.pair 1 (0) + 1
  | .DROP => Nat.pair 2 (0) + 1
  | .SELECT x0 => Nat.pair 3 (Encodable.encode x0) + 1
  | .BLOCK x0 x1 => Nat.pair 4 (Nat.pair (Encodable.encode x0) (encodeInstructions x1)) + 1
  | .LOOP x0 x1 => Nat.pair 5 (Nat.pair (Encodable.encode x0) (encodeInstructions x1)) + 1
  | .«IF % % ELSE %» x0 x1 x2 => Nat.pair 6 (Nat.pair (Encodable.encode x0) (Nat.pair (encodeInstructions x1) (encodeInstructions x2))) + 1
  | .BR x0 => Nat.pair 7 (Encodable.encode x0) + 1
  | .BR_IF x0 => Nat.pair 8 (Encodable.encode x0) + 1
  | .BR_TABLE x0 x1 => Nat.pair 9 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .BR_ON_NULL x0 => Nat.pair 10 (Encodable.encode x0) + 1
  | .BR_ON_NON_NULL x0 => Nat.pair 11 (Encodable.encode x0) + 1
  | .BR_ON_CAST x0 x1 x2 => Nat.pair 12 (Nat.pair (Encodable.encode x0) (Nat.pair (Encodable.encode x1) (Encodable.encode x2))) + 1
  | .BR_ON_CAST_FAIL x0 x1 x2 => Nat.pair 13 (Nat.pair (Encodable.encode x0) (Nat.pair (Encodable.encode x1) (Encodable.encode x2))) + 1
  | .CALL x0 => Nat.pair 14 (Encodable.encode x0) + 1
  | .CALL_REF x0 => Nat.pair 15 (Encodable.encode x0) + 1
  | .CALL_INDIRECT x0 x1 => Nat.pair 16 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .RETURN => Nat.pair 17 (0) + 1
  | .RETURN_CALL x0 => Nat.pair 18 (Encodable.encode x0) + 1
  | .RETURN_CALL_REF x0 => Nat.pair 19 (Encodable.encode x0) + 1
  | .RETURN_CALL_INDIRECT x0 x1 => Nat.pair 20 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .THROW x0 => Nat.pair 21 (Encodable.encode x0) + 1
  | .THROW_REF => Nat.pair 22 (0) + 1
  | .TRY_TABLE x0 x1 x2 => Nat.pair 23 (Nat.pair (Encodable.encode x0) (Nat.pair (Encodable.encode x1) (encodeInstructions x2))) + 1
  | .«LOCAL.GET» x0 => Nat.pair 24 (Encodable.encode x0) + 1
  | .«LOCAL.SET» x0 => Nat.pair 25 (Encodable.encode x0) + 1
  | .«LOCAL.TEE» x0 => Nat.pair 26 (Encodable.encode x0) + 1
  | .«GLOBAL.GET» x0 => Nat.pair 27 (Encodable.encode x0) + 1
  | .«GLOBAL.SET» x0 => Nat.pair 28 (Encodable.encode x0) + 1
  | .«TABLE.GET» x0 => Nat.pair 29 (Encodable.encode x0) + 1
  | .«TABLE.SET» x0 => Nat.pair 30 (Encodable.encode x0) + 1
  | .«TABLE.SIZE» x0 => Nat.pair 31 (Encodable.encode x0) + 1
  | .«TABLE.GROW» x0 => Nat.pair 32 (Encodable.encode x0) + 1
  | .«TABLE.FILL» x0 => Nat.pair 33 (Encodable.encode x0) + 1
  | .«TABLE.COPY» x0 x1 => Nat.pair 34 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«TABLE.INIT» x0 x1 => Nat.pair 35 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«ELEM.DROP» x0 => Nat.pair 36 (Encodable.encode x0) + 1
  | .LOAD x0 x1 => Nat.pair 37 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .STORE x0 x1 => Nat.pair 38 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«VEC.LOAD» x0 x1 => Nat.pair 39 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«VEC.STORE» x0 x1 => Nat.pair 40 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«VEC.LOAD_LANE» x0 x1 x2 => Nat.pair 41 (Nat.pair (Encodable.encode x0) (Nat.pair (Encodable.encode x1) (Encodable.encode x2))) + 1
  | .«VEC.STORE_LANE» x0 x1 x2 => Nat.pair 42 (Nat.pair (Encodable.encode x0) (Nat.pair (Encodable.encode x1) (Encodable.encode x2))) + 1
  | .«MEMORY.SIZE» x0 => Nat.pair 43 (Encodable.encode x0) + 1
  | .«MEMORY.GROW» x0 => Nat.pair 44 (Encodable.encode x0) + 1
  | .«MEMORY.FILL» x0 => Nat.pair 45 (Encodable.encode x0) + 1
  | .«MEMORY.COPY» x0 x1 => Nat.pair 46 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«MEMORY.INIT» x0 x1 => Nat.pair 47 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«DATA.DROP» x0 => Nat.pair 48 (Encodable.encode x0) + 1
  | .«REF.NULL» x0 => Nat.pair 49 (Encodable.encode x0) + 1
  | .«REF.FUNC» x0 => Nat.pair 50 (Encodable.encode x0) + 1
  | .«REF.IS_NULL» => Nat.pair 51 (0) + 1
  | .«REF.AS_NON_NULL» => Nat.pair 52 (0) + 1
  | .«REF.TEST» x0 => Nat.pair 53 (Encodable.encode x0) + 1
  | .«REF.CAST» x0 => Nat.pair 54 (Encodable.encode x0) + 1
  | .«REF.EQ» => Nat.pair 55 (0) + 1
  | .«REF.I31» => Nat.pair 56 (0) + 1
  | .«I31.GET» x0 => Nat.pair 57 (Encodable.encode x0) + 1
  | .«STRUCT.NEW» x0 x1 => Nat.pair 58 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«STRUCT.GET» x0 x1 x2 => Nat.pair 59 (Nat.pair (Encodable.encode x0) (Nat.pair (Encodable.encode x1) (Encodable.encode x2))) + 1
  | .«STRUCT.SET» x0 x1 => Nat.pair 60 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«ARRAY.NEW» x0 x1 => Nat.pair 61 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«ARRAY.NEW_FIXED» x0 x1 => Nat.pair 62 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«ARRAY.NEW_ELEM» x0 x1 => Nat.pair 63 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«ARRAY.NEW_DATA» x0 x1 => Nat.pair 64 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«ARRAY.GET» x0 x1 => Nat.pair 65 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«ARRAY.SET» x0 => Nat.pair 66 (Encodable.encode x0) + 1
  | .«ARRAY.LEN» => Nat.pair 67 (0) + 1
  | .«ARRAY.COPY» x0 x1 => Nat.pair 68 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«ARRAY.FILL» x0 => Nat.pair 69 (Encodable.encode x0) + 1
  | .«ARRAY.INIT_DATA» x0 x1 => Nat.pair 70 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«ARRAY.INIT_ELEM» x0 x1 => Nat.pair 71 (Nat.pair (Encodable.encode x0) (Encodable.encode x1)) + 1
  | .«EXTERN.CONVERT» x0 => Nat.pair 72 (Encodable.encode x0) + 1
  | .CONST x0 => Nat.pair 73 (Encodable.encode x0) + 1
  | .TEST x0 => Nat.pair 74 (Encodable.encode x0) + 1
  | .COMPARE x0 => Nat.pair 75 (Encodable.encode x0) + 1
  | .UNARY x0 => Nat.pair 76 (Encodable.encode x0) + 1
  | .BINOP x0 => Nat.pair 77 (Encodable.encode x0) + 1
  | .CONVERT x0 => Nat.pair 78 (Encodable.encode x0) + 1
  | .«VEC.CONST» x0 => Nat.pair 79 (Encodable.encode x0) + 1
  | .«VEC.TEST» x0 => Nat.pair 80 (Encodable.encode x0) + 1
  | .«VEC.UNARY» x0 => Nat.pair 81 (Encodable.encode x0) + 1
  | .«VEC.BINARY» x0 => Nat.pair 82 (Encodable.encode x0) + 1
  | .«VEC.TERNARY» x0 => Nat.pair 83 (Encodable.encode x0) + 1
  | .«VEC.COMPARE» x0 => Nat.pair 84 (Encodable.encode x0) + 1
  | .«VEC.CONVERT» x0 => Nat.pair 85 (Encodable.encode x0) + 1
  | .«VEC.SHIFT» x0 => Nat.pair 86 (Encodable.encode x0) + 1
  | .«VEC.BITMASK» x0 => Nat.pair 87 (Encodable.encode x0) + 1
  | .«VEC.TESTBITS» x0 => Nat.pair 88 (Encodable.encode x0) + 1
  | .«VEC.UNARYBITS» x0 => Nat.pair 89 (Encodable.encode x0) + 1
  | .«VEC.BINARYBITS» x0 => Nat.pair 90 (Encodable.encode x0) + 1
  | .«VEC.TERNARYBITS» x0 => Nat.pair 91 (Encodable.encode x0) + 1
  | .«VEC.SPLAT» x0 => Nat.pair 92 (Encodable.encode x0) + 1
  | .«VEC.EXTRACT» x0 => Nat.pair 93 (Encodable.encode x0) + 1
  | .«VEC.REPLACE» x0 => Nat.pair 94 (Encodable.encode x0) + 1

def encodeInstructions : List SpecTec.instr → Nat
  | [] => 0
  | x :: xs => Nat.pair (encodeInstruction x) (encodeInstructions xs) + 1

end

mutual

def decodeInstructionFuel : Nat → Nat → Option SpecTec.instr
  | 0, _ => none
  | fuel + 1, 0 => none
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      match p.1 with
      | 0 =>
          some (SpecTec.instr.UNREACHABLE)
      | 1 =>
          some (SpecTec.instr.NOP)
      | 2 =>
          some (SpecTec.instr.DROP)
      | 3 =>
          SpecTec.instr.SELECT <$> (Encodable.decode p.2)
      | 4 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.BLOCK <$> (Encodable.decode q0.1) <*> (decodeInstructionsFuel fuel q0.2)
      | 5 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.LOOP <$> (Encodable.decode q0.1) <*> (decodeInstructionsFuel fuel q0.2)
      | 6 =>
          let q0 := Nat.unpair p.2
          let q1 := Nat.unpair q0.2
          SpecTec.instr.«IF % % ELSE %» <$> (Encodable.decode q0.1) <*> (decodeInstructionsFuel fuel q1.1) <*> (decodeInstructionsFuel fuel q1.2)
      | 7 =>
          SpecTec.instr.BR <$> (Encodable.decode p.2)
      | 8 =>
          SpecTec.instr.BR_IF <$> (Encodable.decode p.2)
      | 9 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.BR_TABLE <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 10 =>
          SpecTec.instr.BR_ON_NULL <$> (Encodable.decode p.2)
      | 11 =>
          SpecTec.instr.BR_ON_NON_NULL <$> (Encodable.decode p.2)
      | 12 =>
          let q0 := Nat.unpair p.2
          let q1 := Nat.unpair q0.2
          SpecTec.instr.BR_ON_CAST <$> (Encodable.decode q0.1) <*> (Encodable.decode q1.1) <*> (Encodable.decode q1.2)
      | 13 =>
          let q0 := Nat.unpair p.2
          let q1 := Nat.unpair q0.2
          SpecTec.instr.BR_ON_CAST_FAIL <$> (Encodable.decode q0.1) <*> (Encodable.decode q1.1) <*> (Encodable.decode q1.2)
      | 14 =>
          SpecTec.instr.CALL <$> (Encodable.decode p.2)
      | 15 =>
          SpecTec.instr.CALL_REF <$> (Encodable.decode p.2)
      | 16 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.CALL_INDIRECT <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 17 =>
          some (SpecTec.instr.RETURN)
      | 18 =>
          SpecTec.instr.RETURN_CALL <$> (Encodable.decode p.2)
      | 19 =>
          SpecTec.instr.RETURN_CALL_REF <$> (Encodable.decode p.2)
      | 20 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.RETURN_CALL_INDIRECT <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 21 =>
          SpecTec.instr.THROW <$> (Encodable.decode p.2)
      | 22 =>
          some (SpecTec.instr.THROW_REF)
      | 23 =>
          let q0 := Nat.unpair p.2
          let q1 := Nat.unpair q0.2
          SpecTec.instr.TRY_TABLE <$> (Encodable.decode q0.1) <*> (Encodable.decode q1.1) <*> (decodeInstructionsFuel fuel q1.2)
      | 24 =>
          SpecTec.instr.«LOCAL.GET» <$> (Encodable.decode p.2)
      | 25 =>
          SpecTec.instr.«LOCAL.SET» <$> (Encodable.decode p.2)
      | 26 =>
          SpecTec.instr.«LOCAL.TEE» <$> (Encodable.decode p.2)
      | 27 =>
          SpecTec.instr.«GLOBAL.GET» <$> (Encodable.decode p.2)
      | 28 =>
          SpecTec.instr.«GLOBAL.SET» <$> (Encodable.decode p.2)
      | 29 =>
          SpecTec.instr.«TABLE.GET» <$> (Encodable.decode p.2)
      | 30 =>
          SpecTec.instr.«TABLE.SET» <$> (Encodable.decode p.2)
      | 31 =>
          SpecTec.instr.«TABLE.SIZE» <$> (Encodable.decode p.2)
      | 32 =>
          SpecTec.instr.«TABLE.GROW» <$> (Encodable.decode p.2)
      | 33 =>
          SpecTec.instr.«TABLE.FILL» <$> (Encodable.decode p.2)
      | 34 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«TABLE.COPY» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 35 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«TABLE.INIT» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 36 =>
          SpecTec.instr.«ELEM.DROP» <$> (Encodable.decode p.2)
      | 37 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.LOAD <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 38 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.STORE <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 39 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«VEC.LOAD» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 40 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«VEC.STORE» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 41 =>
          let q0 := Nat.unpair p.2
          let q1 := Nat.unpair q0.2
          SpecTec.instr.«VEC.LOAD_LANE» <$> (Encodable.decode q0.1) <*> (Encodable.decode q1.1) <*> (Encodable.decode q1.2)
      | 42 =>
          let q0 := Nat.unpair p.2
          let q1 := Nat.unpair q0.2
          SpecTec.instr.«VEC.STORE_LANE» <$> (Encodable.decode q0.1) <*> (Encodable.decode q1.1) <*> (Encodable.decode q1.2)
      | 43 =>
          SpecTec.instr.«MEMORY.SIZE» <$> (Encodable.decode p.2)
      | 44 =>
          SpecTec.instr.«MEMORY.GROW» <$> (Encodable.decode p.2)
      | 45 =>
          SpecTec.instr.«MEMORY.FILL» <$> (Encodable.decode p.2)
      | 46 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«MEMORY.COPY» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 47 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«MEMORY.INIT» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 48 =>
          SpecTec.instr.«DATA.DROP» <$> (Encodable.decode p.2)
      | 49 =>
          SpecTec.instr.«REF.NULL» <$> (Encodable.decode p.2)
      | 50 =>
          SpecTec.instr.«REF.FUNC» <$> (Encodable.decode p.2)
      | 51 =>
          some (SpecTec.instr.«REF.IS_NULL»)
      | 52 =>
          some (SpecTec.instr.«REF.AS_NON_NULL»)
      | 53 =>
          SpecTec.instr.«REF.TEST» <$> (Encodable.decode p.2)
      | 54 =>
          SpecTec.instr.«REF.CAST» <$> (Encodable.decode p.2)
      | 55 =>
          some (SpecTec.instr.«REF.EQ»)
      | 56 =>
          some (SpecTec.instr.«REF.I31»)
      | 57 =>
          SpecTec.instr.«I31.GET» <$> (Encodable.decode p.2)
      | 58 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«STRUCT.NEW» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 59 =>
          let q0 := Nat.unpair p.2
          let q1 := Nat.unpair q0.2
          SpecTec.instr.«STRUCT.GET» <$> (Encodable.decode q0.1) <*> (Encodable.decode q1.1) <*> (Encodable.decode q1.2)
      | 60 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«STRUCT.SET» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 61 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«ARRAY.NEW» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 62 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«ARRAY.NEW_FIXED» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 63 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«ARRAY.NEW_ELEM» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 64 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«ARRAY.NEW_DATA» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 65 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«ARRAY.GET» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 66 =>
          SpecTec.instr.«ARRAY.SET» <$> (Encodable.decode p.2)
      | 67 =>
          some (SpecTec.instr.«ARRAY.LEN»)
      | 68 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«ARRAY.COPY» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 69 =>
          SpecTec.instr.«ARRAY.FILL» <$> (Encodable.decode p.2)
      | 70 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«ARRAY.INIT_DATA» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 71 =>
          let q0 := Nat.unpair p.2
          SpecTec.instr.«ARRAY.INIT_ELEM» <$> (Encodable.decode q0.1) <*> (Encodable.decode q0.2)
      | 72 =>
          SpecTec.instr.«EXTERN.CONVERT» <$> (Encodable.decode p.2)
      | 73 =>
          SpecTec.instr.CONST <$> (Encodable.decode p.2)
      | 74 =>
          SpecTec.instr.TEST <$> (Encodable.decode p.2)
      | 75 =>
          SpecTec.instr.COMPARE <$> (Encodable.decode p.2)
      | 76 =>
          SpecTec.instr.UNARY <$> (Encodable.decode p.2)
      | 77 =>
          SpecTec.instr.BINOP <$> (Encodable.decode p.2)
      | 78 =>
          SpecTec.instr.CONVERT <$> (Encodable.decode p.2)
      | 79 =>
          SpecTec.instr.«VEC.CONST» <$> (Encodable.decode p.2)
      | 80 =>
          SpecTec.instr.«VEC.TEST» <$> (Encodable.decode p.2)
      | 81 =>
          SpecTec.instr.«VEC.UNARY» <$> (Encodable.decode p.2)
      | 82 =>
          SpecTec.instr.«VEC.BINARY» <$> (Encodable.decode p.2)
      | 83 =>
          SpecTec.instr.«VEC.TERNARY» <$> (Encodable.decode p.2)
      | 84 =>
          SpecTec.instr.«VEC.COMPARE» <$> (Encodable.decode p.2)
      | 85 =>
          SpecTec.instr.«VEC.CONVERT» <$> (Encodable.decode p.2)
      | 86 =>
          SpecTec.instr.«VEC.SHIFT» <$> (Encodable.decode p.2)
      | 87 =>
          SpecTec.instr.«VEC.BITMASK» <$> (Encodable.decode p.2)
      | 88 =>
          SpecTec.instr.«VEC.TESTBITS» <$> (Encodable.decode p.2)
      | 89 =>
          SpecTec.instr.«VEC.UNARYBITS» <$> (Encodable.decode p.2)
      | 90 =>
          SpecTec.instr.«VEC.BINARYBITS» <$> (Encodable.decode p.2)
      | 91 =>
          SpecTec.instr.«VEC.TERNARYBITS» <$> (Encodable.decode p.2)
      | 92 =>
          SpecTec.instr.«VEC.SPLAT» <$> (Encodable.decode p.2)
      | 93 =>
          SpecTec.instr.«VEC.EXTRACT» <$> (Encodable.decode p.2)
      | 94 =>
          SpecTec.instr.«VEC.REPLACE» <$> (Encodable.decode p.2)
      | _ => none

def decodeInstructionsFuel : Nat → Nat → Option (List SpecTec.instr)
  | 0, _ => none
  | _ + 1, 0 => some []
  | fuel + 1, code + 1 =>
      let p := Nat.unpair code
      List.cons <$> decodeInstructionFuel fuel p.1 <*> decodeInstructionsFuel fuel p.2

end

theorem decode_fuel_roundtrip (fuel : Nat) :
    (∀ x : SpecTec.instr, instructionDepth x < fuel →
      decodeInstructionFuel fuel (encodeInstruction x) = some x) ∧
    (∀ xs : List SpecTec.instr, instructionsDepth xs < fuel →
      decodeInstructionsFuel fuel (encodeInstructions xs) = some xs) := by
  induction fuel with
  | zero =>
    constructor
    · intro x h
      omega
    · intro xs h
      omega
  | succ fuel ih =>
    constructor
    · intro x h
      cases x with
      | BLOCK b xs =>
        have hxs : instructionsDepth xs < fuel := by
          simp [instructionDepth] at h
          omega
        simp [encodeInstruction, decodeInstructionFuel, Nat.unpair_pair,
          Encodable.encodek, ih.2 xs hxs]
      | LOOP b xs =>
        have hxs : instructionsDepth xs < fuel := by
          simp [instructionDepth] at h
          omega
        simp [encodeInstruction, decodeInstructionFuel, Nat.unpair_pair,
          Encodable.encodek, ih.2 xs hxs]
      | «IF % % ELSE %» b xs ys =>
        have hxs : instructionsDepth xs < fuel := by
          simp [instructionDepth] at h
          omega
        have hys : instructionsDepth ys < fuel := by
          simp [instructionDepth] at h
          omega
        simp [encodeInstruction, decodeInstructionFuel, Nat.unpair_pair,
          Encodable.encodek, ih.2 xs hxs, ih.2 ys hys]
      | TRY_TABLE b cs xs =>
        have hxs : instructionsDepth xs < fuel := by
          simp [instructionDepth] at h
          omega
        simp [encodeInstruction, decodeInstructionFuel, Nat.unpair_pair,
          Encodable.encodek, ih.2 xs hxs]
      | _ =>
        simp [encodeInstruction, decodeInstructionFuel, Nat.unpair_pair,
          Encodable.encodek] <;> exact Equiv.symm_apply_apply _ _
    · intro xs h
      cases xs with
      | nil => simp [encodeInstructions, decodeInstructionsFuel]
      | cons x xs =>
        have hx : instructionDepth x < fuel := by
          simp [instructionsDepth] at h
          omega
        have hxs : instructionsDepth xs < fuel := by
          simp [instructionsDepth] at h
          omega
        simp [encodeInstructions, decodeInstructionsFuel, Nat.unpair_pair,
          ih.1 x hx, ih.2 xs hxs]


def fullEncodeInstruction (i : SpecTec.instr) : Nat :=
  Nat.pair (instructionDepth i + 1) (encodeInstruction i)

def fullDecodeInstruction (n : Nat) : Option SpecTec.instr :=
  let p := Nat.unpair n
  decodeInstructionFuel p.1 p.2

theorem fullInstruction_roundtrip (i : SpecTec.instr) :
    fullDecodeInstruction (fullEncodeInstruction i) = some i := by
  simpa [fullDecodeInstruction, fullEncodeInstruction, Nat.unpair_pair] using
    (decode_fuel_roundtrip (instructionDepth i + 1)).1 i (Nat.lt_succ_self _)

instance : Encodable SpecTec.instr :=
  Encodable.ofLeftInjection fullEncodeInstruction fullDecodeInstruction fullInstruction_roundtrip

example : Encodable (List SpecTec.instr) := inferInstance


end

end properties.wasm_module_not_ok.InstructionCodec
