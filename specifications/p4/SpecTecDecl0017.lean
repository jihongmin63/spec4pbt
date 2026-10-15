import SpecTecDecl0016

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$bin_concat:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_concat:case_2:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_concat:case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_concat:case_3:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_concat:case_4:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_concat:case_4:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_concat:case_5:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_concat:case_5:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$cast_op:case_1:downcast:0» (arg0 : value) : (_root_.Option boolValue) := match arg0 with | ._B field0 => some (boolValue._B field0) | _ => none


def «$cast_op:case_2:downcast:0» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$cast_op:case_3:downcast:0» (arg0 : value) : (_root_.Option errorValue) := match arg0 with | .«ERROR '.' %» field0 => some (errorValue.«ERROR '.' %» field0) | _ => none


def «$cast_op:case_4:downcast:0» (arg0 : value) : (_root_.Option matchKindValue) := match arg0 with | .«MATCH_KIND '.' %» field0 => some (matchKindValue.«MATCH_KIND '.' %» field0) | _ => none


def «$cast_op:case_5:downcast:0» (arg0 : value) : (_root_.Option stringLiteral) := match arg0 with | .«'"' % '"'» field0 => some (stringLiteral.«'"' % '"'» field0) | _ => none


def «$cast_op:case_6:downcast:0» (arg0 : value) : (_root_.Option listValue) := match arg0 with | .«LIST `[ % `]» field0 => some (listValue.«LIST `[ % `]» field0) | _ => none


def «$cast_op:case_7:downcast:0» (arg0 : value) : (_root_.Option tupleValue) := match arg0 with | .«TUPLE `( % `)» field0 => some (tupleValue.«TUPLE `( % `)» field0) | _ => none


def «$cast_op:case_8:downcast:0» (arg0 : value) : (_root_.Option arrayValue) := match arg0 with | .«ARRAY `[ % `]» field0 => some (arrayValue.«ARRAY `[ % `]» field0) | _ => none


def «$cast_op:case_9:downcast:0» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «$cast_op:case_10:downcast:0» (arg0 : value) : (_root_.Option structValue) := match arg0 with | .«STRUCT % `{ % `}» field0 field1 => some (structValue.«STRUCT % `{ % `}» field0 field1) | _ => none


def «$cast_op:case_11:downcast:0» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «$cast_op:case_12:downcast:0» (arg0 : value) : (_root_.Option headerUnionValue) := match arg0 with | .«HEADER_UNION % `{ % `}» field0 field1 => some (headerUnionValue.«HEADER_UNION % `{ % `}» field0 field1) | _ => none


def «$cast_op:case_13:downcast:0» (arg0 : value) : (_root_.Option enumValue) := match arg0 with | .«% '.' %» field0 field1 => some (enumValue.«% '.' %» field0 field1) | .«% '.' % '.' %» field0 field1 field2 => some (enumValue.«% '.' % '.' %» field0 field1 field2) | _ => none


def «$cast_op:case_14:downcast:0» (arg0 : value) : (_root_.Option sequenceValue) := match arg0 with | .«SEQ `( % `)» field0 => some (sequenceValue.«SEQ `( % `)» field0) | .«SEQ `( % ',' '...' `)» field0 => some (sequenceValue.«SEQ `( % ',' '...' `)» field0) | _ => none


def «$cast_op:case_15:downcast:0» (arg0 : value) : (_root_.Option recordValue) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordValue.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordValue.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «$cast_op:case_16:downcast:0» (arg0 : value) : (_root_.Option defaultValue) := match arg0 with | .DEFAULT => some (defaultValue.DEFAULT) | _ => none


def «$cast_op:case_17:downcast:0» (arg0 : value) : (_root_.Option invalidHeaderValue) := match arg0 with | .«'{#}'» => some (invalidHeaderValue.«'{#}'») | _ => none


def «$cast_op:case_18:downcast:0» (arg0 : value) : (_root_.Option setValue) := match arg0 with | .«SET `{ % `}» field0 => some (setValue.«SET `{ % `}» field0) | .«SET `{ % `( % `) `}» field0 field1 => some (setValue.«SET `{ % `( % `) `}» field0 field1) | .«SET `{ % '&&&' % `}» field0 field1 => some (setValue.«SET `{ % '&&&' % `}» field0 field1) | .«SET `{ % '..' % `}» field0 field1 => some (setValue.«SET `{ % '..' % `}» field0 field1) | .«SET `{ '...' `}» => some (setValue.«SET `{ '...' `}») | _ => none


def «$cast_int:case_1:downcast:1» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$cast_int:case_2:downcast:1» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$cast_int:case_3:downcast:1» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$cast_int:case_4:downcast:1» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$cast_int:case_5:downcast:1» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$cast_int:case_6:downcast:1» (arg0 : integerValue) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none

end SpecTec
