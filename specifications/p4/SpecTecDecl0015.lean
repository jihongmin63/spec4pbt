import SpecTecDecl0014

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$bin_lt:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_lt:case_1:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_lt:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_lt:case_2:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_lt:case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_lt:case_3:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_gt:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_gt:case_1:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_gt:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_gt:case_2:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_gt:case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_gt:case_3:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_eq:case_1:downcast:0» (arg0 : value) : (_root_.Option boolValue) := match arg0 with | ._B field0 => some (boolValue._B field0) | _ => none


def «$bin_eq:case_1:downcast:1» (arg0 : value) : (_root_.Option boolValue) := match arg0 with | ._B field0 => some (boolValue._B field0) | _ => none


def «$bin_eq:case_2:downcast:0» (arg0 : value) : (_root_.Option errorValue) := match arg0 with | .«ERROR '.' %» field0 => some (errorValue.«ERROR '.' %» field0) | _ => none


def «$bin_eq:case_2:downcast:1» (arg0 : value) : (_root_.Option errorValue) := match arg0 with | .«ERROR '.' %» field0 => some (errorValue.«ERROR '.' %» field0) | _ => none


def «$bin_eq:case_3:downcast:0» (arg0 : value) : (_root_.Option matchKindValue) := match arg0 with | .«MATCH_KIND '.' %» field0 => some (matchKindValue.«MATCH_KIND '.' %» field0) | _ => none


def «$bin_eq:case_3:downcast:1» (arg0 : value) : (_root_.Option matchKindValue) := match arg0 with | .«MATCH_KIND '.' %» field0 => some (matchKindValue.«MATCH_KIND '.' %» field0) | _ => none


def «$bin_eq:case_4:downcast:0» (arg0 : value) : (_root_.Option stringLiteral) := match arg0 with | .«'"' % '"'» field0 => some (stringLiteral.«'"' % '"'» field0) | _ => none


def «$bin_eq:case_4:downcast:1» (arg0 : value) : (_root_.Option stringLiteral) := match arg0 with | .«'"' % '"'» field0 => some (stringLiteral.«'"' % '"'» field0) | _ => none


def «$bin_eq:case_5:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_eq:case_5:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_eq:case_6:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_eq:case_6:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_eq:case_7:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_eq:case_7:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_eq:case_8:downcast:0» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$bin_eq:case_8:downcast:1» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «$bin_eq:case_9:downcast:0» (arg0 : value) : (_root_.Option listValue) := match arg0 with | .«LIST `[ % `]» field0 => some (listValue.«LIST `[ % `]» field0) | _ => none


def «$bin_eq:case_9:downcast:1» (arg0 : value) : (_root_.Option listValue) := match arg0 with | .«LIST `[ % `]» field0 => some (listValue.«LIST `[ % `]» field0) | _ => none


def «$bin_eq:case_10:downcast:0» (arg0 : value) : (_root_.Option tupleValue) := match arg0 with | .«TUPLE `( % `)» field0 => some (tupleValue.«TUPLE `( % `)» field0) | _ => none


def «$bin_eq:case_10:downcast:1» (arg0 : value) : (_root_.Option tupleValue) := match arg0 with | .«TUPLE `( % `)» field0 => some (tupleValue.«TUPLE `( % `)» field0) | _ => none

end SpecTec
