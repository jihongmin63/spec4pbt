import SpecTecDecl0011

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$un_plus:case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$un_minus:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$un_minus:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$un_minus:case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_plus:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_plus:case_1:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_plus:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_plus:case_2:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_plus:case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_plus:case_3:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satplus:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satplus:case_1:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satplus:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satplus:case_2:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satplus:case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satplus:case_3:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_minus:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_minus:case_1:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_minus:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_minus:case_2:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_minus:case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_minus:case_3:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satminus:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satminus:case_1:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satminus:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satminus:case_2:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satminus:case_3:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_satminus:case_3:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_mul:case_1:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_mul:case_1:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_mul:case_2:downcast:0» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «$bin_mul:case_2:downcast:1» (arg0 : value) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none

end SpecTec
