import SpecTecDecl0015

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$bin_eq:case_11:downcast:0» (arg0 : value) : (_root_.Option sequenceValue) := match arg0 with | .«SEQ `( % `)» field0 => some (sequenceValue.«SEQ `( % `)» field0) | .«SEQ `( % ',' '...' `)» field0 => some (sequenceValue.«SEQ `( % ',' '...' `)» field0) | _ => none


def «$bin_eq:case_11:downcast:1» (arg0 : value) : (_root_.Option sequenceValue) := match arg0 with | .«SEQ `( % `)» field0 => some (sequenceValue.«SEQ `( % `)» field0) | .«SEQ `( % ',' '...' `)» field0 => some (sequenceValue.«SEQ `( % ',' '...' `)» field0) | _ => none


def «$bin_eq:case_12:downcast:0» (arg0 : value) : (_root_.Option arrayValue) := match arg0 with | .«ARRAY `[ % `]» field0 => some (arrayValue.«ARRAY `[ % `]» field0) | _ => none


def «$bin_eq:case_12:downcast:1» (arg0 : value) : (_root_.Option arrayValue) := match arg0 with | .«ARRAY `[ % `]» field0 => some (arrayValue.«ARRAY `[ % `]» field0) | _ => none


def «$bin_eq:case_13:downcast:0» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «$bin_eq:case_13:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «$bin_eq:case_14:downcast:0» (arg0 : value) : (_root_.Option structValue) := match arg0 with | .«STRUCT % `{ % `}» field0 field1 => some (structValue.«STRUCT % `{ % `}» field0 field1) | _ => none


def «$bin_eq:case_14:downcast:1» (arg0 : value) : (_root_.Option structValue) := match arg0 with | .«STRUCT % `{ % `}» field0 field1 => some (structValue.«STRUCT % `{ % `}» field0 field1) | _ => none


def «$bin_eq:case_15:downcast:0» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «$bin_eq:case_15:downcast:1» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «$bin_eq:case_16:downcast:0» (arg0 : value) : (_root_.Option headerUnionValue) := match arg0 with | .«HEADER_UNION % `{ % `}» field0 field1 => some (headerUnionValue.«HEADER_UNION % `{ % `}» field0 field1) | _ => none


def «$bin_eq:case_16:downcast:1» (arg0 : value) : (_root_.Option headerUnionValue) := match arg0 with | .«HEADER_UNION % `{ % `}» field0 field1 => some (headerUnionValue.«HEADER_UNION % `{ % `}» field0 field1) | _ => none


def «$bin_eq:case_17:downcast:0» (arg0 : value) : (_root_.Option enumValue) := match arg0 with | .«% '.' %» field0 field1 => some (enumValue.«% '.' %» field0 field1) | .«% '.' % '.' %» field0 field1 field2 => some (enumValue.«% '.' % '.' %» field0 field1 field2) | _ => none


def «$bin_eq:case_17:downcast:1» (arg0 : value) : (_root_.Option enumValue) := match arg0 with | .«% '.' %» field0 field1 => some (enumValue.«% '.' %» field0 field1) | .«% '.' % '.' %» field0 field1 field2 => some (enumValue.«% '.' % '.' %» field0 field1 field2) | _ => none


def «$bin_eq:case_18:downcast:0» (arg0 : value) : (_root_.Option enumValue) := match arg0 with | .«% '.' %» field0 field1 => some (enumValue.«% '.' %» field0 field1) | .«% '.' % '.' %» field0 field1 field2 => some (enumValue.«% '.' % '.' %» field0 field1 field2) | _ => none


def «$bin_eq:case_18:downcast:1» (arg0 : value) : (_root_.Option enumValue) := match arg0 with | .«% '.' %» field0 field1 => some (enumValue.«% '.' %» field0 field1) | .«% '.' % '.' %» field0 field1 field2 => some (enumValue.«% '.' % '.' %» field0 field1 field2) | _ => none


def «$bin_eq:case_19:downcast:0» (arg0 : value) : (_root_.Option invalidHeaderValue) := match arg0 with | .«'{#}'» => some (invalidHeaderValue.«'{#}'») | _ => none


def «$bin_eq:case_19:downcast:1» (arg0 : value) : (_root_.Option invalidHeaderValue) := match arg0 with | .«'{#}'» => some (invalidHeaderValue.«'{#}'») | _ => none


def «$bin_band:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_band:case_1:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_band:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_band:case_2:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_bxor:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_bxor:case_1:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_bxor:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_bxor:case_2:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_bor:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_bor:case_1:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_bor:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_bor:case_2:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_concat:case_1:downcast:0» (arg0 : value) : (_root_.Option stringLiteral) := match arg0 with | .«'"' % '"'» field0 => some (stringLiteral.«'"' % '"'» field0) | _ => none


def «$bin_concat:case_1:downcast:1» (arg0 : value) : (_root_.Option stringLiteral) := match arg0 with | .«'"' % '"'» field0 => some (stringLiteral.«'"' % '"'» field0) | _ => none

end SpecTec
