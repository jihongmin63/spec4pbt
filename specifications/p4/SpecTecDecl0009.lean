import SpecTecDecl0008

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

inductive sequenceValue : Type where
  | «SEQ `( % `)» : (_root_.List value) → sequenceValue
  | «SEQ `( % ',' '...' `)» : (_root_.List value) → sequenceValue
deriving _root_.DecidableEq


inductive recordValue : Type where
  | «RECORD `{ % `}» : (_root_.List fieldValue) → recordValue
  | «RECORD `{ % ',' '...' `}» : (_root_.List fieldValue) → recordValue
deriving _root_.DecidableEq


inductive setValue : Type where
  | «SET `{ % `}» : value → setValue
  | «SET `{ % `( % `) `}» : (_root_.List value) → _root_.Nat → setValue
  | «SET `{ % '&&&' % `}» : value → value → setValue
  | «SET `{ % '..' % `}» : value → value → setValue
  | «SET `{ '...' `}» : setValue
deriving _root_.DecidableEq


inductive tableMetadataStructValue : Type where
  | «TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» : typeId → boolValue → boolValue → tableMetadataEnumValue → tableMetadataStructValue
deriving _root_.DecidableEq


inductive tableMetadataValue : Type where
  | «TABLE_ENUM % '.' %» : typeId → nameIR → tableMetadataValue
  | «TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» : typeId → boolValue → boolValue → tableMetadataEnumValue → tableMetadataValue
deriving _root_.DecidableEq


inductive synthesizedValue : Type where
  | DEFAULT : synthesizedValue
  | «'{#}'» : synthesizedValue
  | «SEQ `( % `)» : (_root_.List value) → synthesizedValue
  | «SEQ `( % ',' '...' `)» : (_root_.List value) → synthesizedValue
  | «RECORD `{ % `}» : (_root_.List fieldValue) → synthesizedValue
  | «RECORD `{ % ',' '...' `}» : (_root_.List fieldValue) → synthesizedValue
  | «SET `{ % `}» : value → synthesizedValue
  | «SET `{ % `( % `) `}» : (_root_.List value) → _root_.Nat → synthesizedValue
  | «SET `{ % '&&&' % `}» : value → value → synthesizedValue
  | «SET `{ % '..' % `}» : value → value → synthesizedValue
  | «SET `{ '...' `}» : synthesizedValue
  | «TABLE_ENUM % '.' %» : typeId → nameIR → synthesizedValue
  | «TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» : typeId → boolValue → boolValue → tableMetadataEnumValue → synthesizedValue
deriving _root_.DecidableEq


abbrev bit : Type := _root_.Bool


abbrev bits : Type := (_root_.List bit)


def «$bits_to_int_unsigned» (arg0 : bits) : _root_.Int := arg0.foldl (fun value bit => 2 * value + (if bit then 1 else 0)) (0 : Int)


def «$bits_to_int_signed:convert» (arg0 : bits) : _root_.Int := match arg0 with | [] => 0 | sign :: _ => let unsigned := arg0.foldl (fun value bit => 2 * value + (if bit then 1 else 0)) (0 : Int); if sign then unsigned - (2 : Int) ^ arg0.length else unsigned


def «$int_of_integerValue:case_1:downcast:0» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$int_of_integerValue:case_2:downcast:0» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$int_of_integerValue:case_3:downcast:0» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$update_headerUnion:case_3:downcast:0» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «$isValid_header:case_1:downcast:0» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «$invalidate_value:case_1:downcast:0» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «$invalidate_value:case_2:downcast:0» (arg0 : value) : (_root_.Option headerUnionValue) := match arg0 with | .«HEADER_UNION % `{ % `}» field0 field1 => some (headerUnionValue.«HEADER_UNION % `{ % `}» field0 field1) | _ => none


def «$write_value_from_bits':case_1:downcast:0» (arg0 : value) : (_root_.Option boolValue) := match arg0 with | ._B field0 => some (boolValue._B field0) | _ => none


def «$write_value_from_bits':case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$write_value_from_bits':case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$write_value_from_bits':case_4:downcast:0» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$write_value_from_bits':case_5:downcast:0» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$write_value_from_bits':case_6:downcast:0» (arg0 : value) : (_root_.Option structValue) := match arg0 with | .«STRUCT % `{ % `}» field0 field1 => some (structValue.«STRUCT % `{ % `}» field0 field1) | _ => none


def «$write_value_from_bits':case_7:downcast:0» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «$write_value_from_bits':case_8:downcast:0» (arg0 : value) : (_root_.Option enumValue) := match arg0 with | .«% '.' %» field0 field1 => some (enumValue.«% '.' %» field0 field1) | .«% '.' % '.' %» field0 field1 field2 => some (enumValue.«% '.' % '.' %» field0 field1 field2) | _ => none


def «$write_value_from_bits':case_9:downcast:0» (arg0 : value) : (_root_.Option arrayValue) := match arg0 with | .«ARRAY `[ % `]» field0 => some (arrayValue.«ARRAY `[ % `]» field0) | _ => none


def «$write_value_from_bits':case_10:downcast:0» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «$write_bits_from_value:case_1:downcast:0» (arg0 : value) : (_root_.Option boolValue) := match arg0 with | ._B field0 => some (boolValue._B field0) | _ => none


def «$write_bits_from_value:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$write_bits_from_value:case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$write_bits_from_value:case_4:downcast:0» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$write_bits_from_value:case_5:downcast:0» (arg0 : value) : (_root_.Option arrayValue) := match arg0 with | .«ARRAY `[ % `]» field0 => some (arrayValue.«ARRAY `[ % `]» field0) | _ => none

end SpecTec
