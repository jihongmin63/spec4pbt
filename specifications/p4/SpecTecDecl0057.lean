import SpecTecDecl0056

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Expr_ok:integerLiteral-fixint:downcast:0» (arg0 : expression) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «Expr_ok:integerLiteral-fixbit:downcast:0» (arg0 : expression) : (_root_.Option integerLiteral) := match arg0 with | .D field0 => some (integerLiteral.D field0) | .«% W %» field0 field1 => some (integerLiteral.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerLiteral.«% S %» field0 field1) | _ => none


def «Expr_ok:stringLiteral:downcast:0» (arg0 : expression) : (_root_.Option stringLiteral) := match arg0 with | .«'"' % '"'» field0 => some (stringLiteral.«'"' % '"'» field0) | _ => none


def «Expr_ok:prefixedNonTypeName:downcast:0» (arg0 : expression) : (_root_.Option prefixedNonTypeName) := match arg0 with | ._ID field0 => some (prefixedNonTypeName._ID field0) | .APPLY => some (prefixedNonTypeName.APPLY) | .KEY => some (prefixedNonTypeName.KEY) | .ACTIONS => some (prefixedNonTypeName.ACTIONS) | .STATE => some (prefixedNonTypeName.STATE) | .ENTRIES => some (prefixedNonTypeName.ENTRIES) | .TYPE => some (prefixedNonTypeName.TYPE) | .PRIORITY => some (prefixedNonTypeName.PRIORITY) | .«_ID '.' %» field0 => some (prefixedNonTypeName.«_ID '.' %» field0) | _ => none


def «Expr_ok:defaultExpression:downcast:0» (arg0 : expression) : (_root_.Option defaultExpression) := match arg0 with | .«'...'» => some (defaultExpression.«'...'») | _ => none


def «Expr_ok:unaryExpression-lnot:downcast:0» (arg0 : expression) : (_root_.Option unaryExpression) := match arg0 with | .«% %» field0 field1 => some (unaryExpression.«% %» field0 field1) | _ => none


def «Expr_ok:unaryExpression-bnot:downcast:0» (arg0 : expression) : (_root_.Option unaryExpression) := match arg0 with | .«% %» field0 field1 => some (unaryExpression.«% %» field0 field1) | _ => none


def «Expr_ok:unaryExpression-uplusminus:downcast:0» (arg0 : expression) : (_root_.Option unaryExpression) := match arg0 with | .«% %» field0 field1 => some (unaryExpression.«% %» field0 field1) | _ => none


def «Expr_ok:binaryExpression-plusminusmult:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «Expr_ok:binaryExpression-satplusminus:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «Expr_ok:rhs-lctk:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «Expr_ok:rhs-lctk:downcast:6» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Expr_ok:rhs-non-lctk:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «Expr_ok:rhs-fixbit:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «Expr_ok:rhs-fixbit:downcast:7» (arg0 : typeIR) : (_root_.Option fixedBitTypeIR) := match arg0 with | .«BIT `< % `>» field0 => some (fixedBitTypeIR.«BIT `< % `>» field0) | _ => none


def «Expr_ok:rhs-non-fixbit:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «Expr_ok:rhs-non-fixbit:downcast:6» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Expr_ok:binaryExpression-equality:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «Expr_ok:binaryExpression-comparison:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «Expr_ok:binaryExpression-bitwise:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «Expr_ok:binaryExpression-concat:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «Expr_ok:binaryExpression-logical:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «Expr_ok:ternaryExpression:downcast:0» (arg0 : expression) : (_root_.Option ternaryExpression) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpression.«% '?' % ':' %» field0 field1 field2) | _ => none


def «Expr_ok:castExpression:downcast:0» (arg0 : expression) : (_root_.Option castExpression) := match arg0 with | .«`( % `) %» field0 field1 => some (castExpression.«`( % `) %» field0 field1) | _ => none


def «Expr_ok:invalidHeaderExpression:downcast:0» (arg0 : expression) : (_root_.Option invalidHeaderExpression) := match arg0 with | .«'{#}'» => some (invalidHeaderExpression.«'{#}'») | _ => none


def «Expr_ok:non-default:downcast:0» (arg0 : expression) : (_root_.Option sequenceOrRecordExpression) := match arg0 with | .«`{ % % `}» field0 field1 => some (sequenceOrRecordExpression.«`{ % % `}» field0 field1) | _ => none


def «Expr_ok:non-default:downcast:1» (arg0 : sequenceOrRecordElementExpression) : (_root_.Option expressionList) := match arg0 with | ._EMPTY => some (expressionList._EMPTY) | .TRUE => some (expressionList.TRUE) | .FALSE => some (expressionList.FALSE) | .D field0 => some (expressionList.D field0) | .«% W %» field0 field1 => some (expressionList.«% W %» field0 field1) | .«% S %» field0 field1 => some (expressionList.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expressionList.«'"' % '"'» field0) | ._ID field0 => some (expressionList._ID field0) | .APPLY => some (expressionList.APPLY) | .KEY => some (expressionList.KEY) | .ACTIONS => some (expressionList.ACTIONS) | .STATE => some (expressionList.STATE) | .ENTRIES => some (expressionList.ENTRIES) | .TYPE => some (expressionList.TYPE) | .PRIORITY => some (expressionList.PRIORITY) | .«_ID '.' %» field0 => some (expressionList.«_ID '.' %» field0) | .THIS => some (expressionList.THIS) | .«'...'» => some (expressionList.«'...'») | .«% %» field0 field1 => some (expressionList.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expressionList.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expressionList.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expressionList.«`( % `) %» field0 field1) | .«'{#}'» => some (expressionList.«'{#}'») | .«`{ % % `}» field0 field1 => some (expressionList.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expressionList.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expressionList.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expressionList.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expressionList.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expressionList.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expressionList.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expressionList.«`( % `)» field0) | .«% ',' %» field0 field1 => some (expressionList.«% ',' %» field0 field1) | _ => none


def «Expr_ok:default:downcast:0» (arg0 : expression) : (_root_.Option sequenceOrRecordExpression) := match arg0 with | .«`{ % % `}» field0 field1 => some (sequenceOrRecordExpression.«`{ % % `}» field0 field1) | _ => none


def «Expr_ok:default:downcast:1» (arg0 : sequenceOrRecordElementExpression) : (_root_.Option expressionList) := match arg0 with | ._EMPTY => some (expressionList._EMPTY) | .TRUE => some (expressionList.TRUE) | .FALSE => some (expressionList.FALSE) | .D field0 => some (expressionList.D field0) | .«% W %» field0 field1 => some (expressionList.«% W %» field0 field1) | .«% S %» field0 field1 => some (expressionList.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expressionList.«'"' % '"'» field0) | ._ID field0 => some (expressionList._ID field0) | .APPLY => some (expressionList.APPLY) | .KEY => some (expressionList.KEY) | .ACTIONS => some (expressionList.ACTIONS) | .STATE => some (expressionList.STATE) | .ENTRIES => some (expressionList.ENTRIES) | .TYPE => some (expressionList.TYPE) | .PRIORITY => some (expressionList.PRIORITY) | .«_ID '.' %» field0 => some (expressionList.«_ID '.' %» field0) | .THIS => some (expressionList.THIS) | .«'...'» => some (expressionList.«'...'») | .«% %» field0 field1 => some (expressionList.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expressionList.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expressionList.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expressionList.«`( % `) %» field0 field1) | .«'{#}'» => some (expressionList.«'{#}'») | .«`{ % % `}» field0 field1 => some (expressionList.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expressionList.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expressionList.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expressionList.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expressionList.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expressionList.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expressionList.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expressionList.«`( % `)» field0) | .«% ',' %» field0 field1 => some (expressionList.«% ',' %» field0 field1) | _ => none


def «Expr_ok:default:downcast:3» (arg0 : expression) : (_root_.Option defaultExpression) := match arg0 with | .«'...'» => some (defaultExpression.«'...'») | _ => none


def «Expr_ok:single-non-default:downcast:0» (arg0 : expression) : (_root_.Option sequenceOrRecordExpression) := match arg0 with | .«`{ % % `}» field0 field1 => some (sequenceOrRecordExpression.«`{ % % `}» field0 field1) | _ => none


def «Expr_ok:single-non-default:downcast:1» (arg0 : sequenceOrRecordElementExpression) : (_root_.Option recordElementExpression) := match arg0 with | .«% '=' %» field0 field1 => some (recordElementExpression.«% '=' %» field0 field1) | .«% '=' % ',' '...'» field0 field1 => some (recordElementExpression.«% '=' % ',' '...'» field0 field1) | .«% '=' % ',' %» field0 field1 field2 => some (recordElementExpression.«% '=' % ',' %» field0 field1 field2) | .«% '=' % ',' % ',' '...'» field0 field1 field2 => some (recordElementExpression.«% '=' % ',' % ',' '...'» field0 field1 field2) | _ => none

end SpecTec
