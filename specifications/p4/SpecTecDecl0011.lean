import SpecTecDecl0010

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$width_of_integerTypeIR:case_4:downcast:0» (arg0 : integerTypeIR) : (_root_.Option varBitTypeIR) := match arg0 with | .«VARBIT `< % `>» field0 => some (varBitTypeIR.«VARBIT `< % `>» field0) | _ => none


inductive constantInitializerIR : Type where
  | «'=' _VALUE %» : value → constantInitializerIR
deriving _root_.DecidableEq


inductive builtinIsValidMethodTypeIR : Type where
  | BUILTIN_IS_VALID : builtinIsValidMethodTypeIR
deriving _root_.DecidableEq


inductive builtinSetValidMethodTypeIR : Type where
  | BUILTIN_SET_VALID : builtinSetValidMethodTypeIR
deriving _root_.DecidableEq


inductive builtinSetInvalidMethodTypeIR : Type where
  | BUILTIN_SET_INVALID : builtinSetInvalidMethodTypeIR
deriving _root_.DecidableEq


inductive builtinPushFrontMethodTypeIR : Type where
  | BUILTIN_PUSH_FRONT : builtinPushFrontMethodTypeIR
deriving _root_.DecidableEq


inductive builtinPopFrontMethodTypeIR : Type where
  | BUILTIN_POP_FRONT : builtinPopFrontMethodTypeIR
deriving _root_.DecidableEq


inductive builtinSizeMethodTypeIR : Type where
  | BUILTIN_SIZE_OF : builtinSizeMethodTypeIR
deriving _root_.DecidableEq


inductive builtinMethodTypeIR : Type where
  | BUILTIN_IS_VALID : builtinMethodTypeIR
  | BUILTIN_SET_VALID : builtinMethodTypeIR
  | BUILTIN_SET_INVALID : builtinMethodTypeIR
  | BUILTIN_PUSH_FRONT : builtinMethodTypeIR
  | BUILTIN_POP_FRONT : builtinMethodTypeIR
  | BUILTIN_SIZE_OF : builtinMethodTypeIR
deriving _root_.DecidableEq


def «$signature_of_builtinMethodTypeIR:case_1:downcast:0» (arg0 : builtinMethodTypeIR) : (_root_.Option builtinIsValidMethodTypeIR) := match arg0 with | .BUILTIN_IS_VALID => some (builtinIsValidMethodTypeIR.BUILTIN_IS_VALID) | _ => none


def «$signature_of_builtinMethodTypeIR:case_2:downcast:0» (arg0 : builtinMethodTypeIR) : (_root_.Option builtinSetValidMethodTypeIR) := match arg0 with | .BUILTIN_SET_VALID => some (builtinSetValidMethodTypeIR.BUILTIN_SET_VALID) | _ => none


def «$signature_of_builtinMethodTypeIR:case_3:downcast:0» (arg0 : builtinMethodTypeIR) : (_root_.Option builtinSetInvalidMethodTypeIR) := match arg0 with | .BUILTIN_SET_INVALID => some (builtinSetInvalidMethodTypeIR.BUILTIN_SET_INVALID) | _ => none


def «$signature_of_builtinMethodTypeIR:case_4:downcast:0» (arg0 : builtinMethodTypeIR) : (_root_.Option builtinPushFrontMethodTypeIR) := match arg0 with | .BUILTIN_PUSH_FRONT => some (builtinPushFrontMethodTypeIR.BUILTIN_PUSH_FRONT) | _ => none


def «$signature_of_builtinMethodTypeIR:case_5:downcast:0» (arg0 : builtinMethodTypeIR) : (_root_.Option builtinPopFrontMethodTypeIR) := match arg0 with | .BUILTIN_POP_FRONT => some (builtinPopFrontMethodTypeIR.BUILTIN_POP_FRONT) | _ => none


def «$signature_of_builtinMethodTypeIR:case_6:downcast:0» (arg0 : builtinMethodTypeIR) : (_root_.Option builtinSizeMethodTypeIR) := match arg0 with | .BUILTIN_SIZE_OF => some (builtinSizeMethodTypeIR.BUILTIN_SIZE_OF) | _ => none


inductive tableApplyMethodTypeIR : Type where
  | «TABLE_APPLY ':' %» : tableMetadataStructTypeIR → tableApplyMethodTypeIR
deriving _root_.DecidableEq


abbrev tableApplyMethodTypeDefIR : Type := tableApplyMethodTypeIR


abbrev bound : Type := (set typeId)


inductive ctk : Type where
  | LCTK : ctk
  | CTK : ctk
  | DYN : ctk
deriving _root_.DecidableEq


def «$pow2» (arg0 : _root_.Nat) : _root_.Int := (2 : Int) ^ arg0


def «$bneg» (arg0 : _root_.Int) : _root_.Int := -arg0 - 1


def «$band» (arg0 : _root_.Int) (arg1 : _root_.Int) : _root_.Int := match arg0, arg1 with | Int.ofNat a, Int.ofNat b => Int.ofNat (Nat.land a b) | Int.ofNat a, Int.negSucc b => Int.ofNat (a - Nat.land a b) | Int.negSucc a, Int.ofNat b => Int.ofNat (b - Nat.land a b) | Int.negSucc a, Int.negSucc b => Int.negSucc (Nat.lor a b)


def «$bxor» (arg0 : _root_.Int) (arg1 : _root_.Int) : _root_.Int := match arg0, arg1 with | Int.ofNat a, Int.ofNat b => Int.ofNat (Nat.xor a b) | Int.ofNat a, Int.negSucc b => Int.negSucc (Nat.xor a b) | Int.negSucc a, Int.ofNat b => Int.negSucc (Nat.xor a b) | Int.negSucc a, Int.negSucc b => Int.ofNat (Nat.xor a b)


def «$bor» (arg0 : _root_.Int) (arg1 : _root_.Int) : _root_.Int := match arg0, arg1 with | Int.ofNat a, Int.ofNat b => Int.ofNat (Nat.lor a b) | Int.ofNat a, Int.negSucc b => Int.negSucc (b - Nat.land a b) | Int.negSucc a, Int.ofNat b => Int.negSucc (a - Nat.land a b) | Int.negSucc a, Int.negSucc b => Int.negSucc (Nat.land a b)


def «$bitacc:band» (arg0 : _root_.Int) (arg1 : _root_.Int) : _root_.Int := match arg0, arg1 with | Int.ofNat a, Int.ofNat b => Int.ofNat (Nat.land a b) | Int.ofNat a, Int.negSucc b => Int.ofNat (a - Nat.land a b) | Int.negSucc a, Int.ofNat b => Int.ofNat (b - Nat.land a b) | Int.negSucc a, Int.negSucc b => Int.negSucc (Nat.lor a b)


def «$bitacc_replace:band» (arg0 : _root_.Int) (arg1 : _root_.Int) : _root_.Int := match arg0, arg1 with | Int.ofNat a, Int.ofNat b => Int.ofNat (Nat.land a b) | Int.ofNat a, Int.negSucc b => Int.ofNat (a - Nat.land a b) | Int.negSucc a, Int.ofNat b => Int.ofNat (b - Nat.land a b) | Int.negSucc a, Int.negSucc b => Int.negSucc (Nat.lor a b)


def «$bitacc_replace:bxor» (arg0 : _root_.Int) (arg1 : _root_.Int) : _root_.Int := match arg0, arg1 with | Int.ofNat a, Int.ofNat b => Int.ofNat (Nat.xor a b) | Int.ofNat a, Int.negSucc b => Int.negSucc (Nat.xor a b) | Int.negSucc a, Int.ofNat b => Int.negSucc (Nat.xor a b) | Int.negSucc a, Int.negSucc b => Int.ofNat (Nat.xor a b)


def «$un_bnot:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$un_bnot:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$un_lnot:case_1:downcast:0» (arg0 : value) : (_root_.Option boolValue) := match arg0 with | ._B field0 => some (boolValue._B field0) | _ => none


def «$un_plus:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$un_plus:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none

end SpecTec
