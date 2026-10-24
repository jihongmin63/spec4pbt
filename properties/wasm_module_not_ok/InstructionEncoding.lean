import properties.wasm_module_not_ok.Enumeration

set_option autoImplicit false

namespace properties.wasm_module_not_ok.InstructionEncoding

mutual

def instructionDepth : SpecTec.instr → Nat
  | .BLOCK _ xs => instructionsDepth xs + 1
  | .LOOP _ xs => instructionsDepth xs + 1
  | .«IF % % ELSE %» _ xs ys => max (instructionsDepth xs) (instructionsDepth ys) + 1
  | .TRY_TABLE _ _ xs => instructionsDepth xs + 1
  | _ => 1

def instructionsDepth : List SpecTec.instr → Nat
  | [] => 0
  | x :: xs => max (instructionDepth x) (instructionsDepth xs) + 1

end

theorem depth_block_child (b : SpecTec.blocktype) (xs : List SpecTec.instr) :
    instructionsDepth xs < instructionDepth (.BLOCK b xs) := by
  simp [instructionDepth]

theorem depth_loop_child (b : SpecTec.blocktype) (xs : List SpecTec.instr) :
    instructionsDepth xs < instructionDepth (.LOOP b xs) := by
  simp [instructionDepth]

theorem depth_if_left_child (b : SpecTec.blocktype)
    (xs ys : List SpecTec.instr) :
    instructionsDepth xs < instructionDepth (.«IF % % ELSE %» b xs ys) := by
  simp only [instructionDepth]
  exact Nat.lt_succ_of_le (Nat.le_max_left _ _)

theorem depth_if_right_child (b : SpecTec.blocktype)
    (xs ys : List SpecTec.instr) :
    instructionsDepth ys < instructionDepth (.«IF % % ELSE %» b xs ys) := by
  simp only [instructionDepth]
  exact Nat.lt_succ_of_le (Nat.le_max_right _ _)

theorem depth_try_child (b : SpecTec.blocktype)
    (cs : List SpecTec.«catch») (xs : List SpecTec.instr) :
    instructionsDepth xs < instructionDepth (.TRY_TABLE b cs xs) := by
  simp [instructionDepth]

theorem depth_cons_head (x : SpecTec.instr) (xs : List SpecTec.instr) :
    instructionDepth x < instructionsDepth (x :: xs) := by
  simp only [instructionsDepth]
  exact Nat.lt_succ_of_le (Nat.le_max_left _ _)

theorem depth_cons_tail (x : SpecTec.instr) (xs : List SpecTec.instr) :
    instructionsDepth xs < instructionsDepth (x :: xs) := by
  simp only [instructionsDepth]
  exact Nat.lt_succ_of_le (Nat.le_max_right _ _)

end properties.wasm_module_not_ok.InstructionEncoding
