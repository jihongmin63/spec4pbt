import SpecTecDecl0002

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «$expressionNonBrace_as_expression:case_7:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option errorAccessExpression) := match arg0 with | .«ERROR '.' %» field0 => some (errorAccessExpression.«ERROR '.' %» field0) | _ => none


def «$expressionNonBrace_as_expression:case_8:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option memberAccessExpressionNonBrace) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionNonBrace.«% '.' %» field0 field1) | _ => none


def «$expressionNonBrace_as_expression:case_8:downcast:1» (arg0 : memberAccessBaseNonBrace) : (_root_.Option prefixedTypeName) := match arg0 with | ._TID field0 => some (prefixedTypeName._TID field0) | .«_TID '.' %» field0 => some (prefixedTypeName.«_TID '.' %» field0) | _ => none


def «$expressionNonBrace_as_expression:case_9:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option memberAccessExpressionNonBrace) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionNonBrace.«% '.' %» field0 field1) | _ => none


def «$expressionNonBrace_as_expression:case_9:downcast:1» (arg0 : memberAccessBaseNonBrace) : (_root_.Option expressionNonBrace) := match arg0 with | .TRUE => some (expressionNonBrace.TRUE) | .FALSE => some (expressionNonBrace.FALSE) | .D field0 => some (expressionNonBrace.D field0) | .«% W %» field0 field1 => some (expressionNonBrace.«% W %» field0 field1) | .«% S %» field0 field1 => some (expressionNonBrace.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expressionNonBrace.«'"' % '"'» field0) | ._ID field0 => some (expressionNonBrace._ID field0) | .APPLY => some (expressionNonBrace.APPLY) | .KEY => some (expressionNonBrace.KEY) | .ACTIONS => some (expressionNonBrace.ACTIONS) | .STATE => some (expressionNonBrace.STATE) | .ENTRIES => some (expressionNonBrace.ENTRIES) | .TYPE => some (expressionNonBrace.TYPE) | .PRIORITY => some (expressionNonBrace.PRIORITY) | .«_ID '.' %» field0 => some (expressionNonBrace.«_ID '.' %» field0) | .THIS => some (expressionNonBrace.THIS) | .«% %» field0 field1 => some (expressionNonBrace.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expressionNonBrace.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expressionNonBrace.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expressionNonBrace.«`( % `) %» field0 field1) | .«ERROR '.' %» field0 => some (expressionNonBrace.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expressionNonBrace.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expressionNonBrace.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expressionNonBrace.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expressionNonBrace.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expressionNonBrace.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expressionNonBrace.«`( % `)» field0) | _ => none


def «$expressionNonBrace_as_expression:case_10:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option indexAccessExpressionNonBrace) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpressionNonBrace.«% `[ % `]» field0 field1) | _ => none


def «$expressionNonBrace_as_expression:case_11:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option sliceAccessExpressionNonBrace) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpressionNonBrace.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «$expressionNonBrace_as_expression:case_12:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option sliceAccessExpressionNonBrace) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpressionNonBrace.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «$expressionNonBrace_as_expression:case_13:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option callExpressionNonBrace) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionNonBrace.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionNonBrace.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «$expressionNonBrace_as_expression:case_13:downcast:1» (arg0 : callTargetNonBrace) : (_root_.Option expressionNonBrace) := match arg0 with | .TRUE => some (expressionNonBrace.TRUE) | .FALSE => some (expressionNonBrace.FALSE) | .D field0 => some (expressionNonBrace.D field0) | .«% W %» field0 field1 => some (expressionNonBrace.«% W %» field0 field1) | .«% S %» field0 field1 => some (expressionNonBrace.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expressionNonBrace.«'"' % '"'» field0) | ._ID field0 => some (expressionNonBrace._ID field0) | .APPLY => some (expressionNonBrace.APPLY) | .KEY => some (expressionNonBrace.KEY) | .ACTIONS => some (expressionNonBrace.ACTIONS) | .STATE => some (expressionNonBrace.STATE) | .ENTRIES => some (expressionNonBrace.ENTRIES) | .TYPE => some (expressionNonBrace.TYPE) | .PRIORITY => some (expressionNonBrace.PRIORITY) | .«_ID '.' %» field0 => some (expressionNonBrace.«_ID '.' %» field0) | .THIS => some (expressionNonBrace.THIS) | .«% %» field0 field1 => some (expressionNonBrace.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expressionNonBrace.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expressionNonBrace.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expressionNonBrace.«`( % `) %» field0 field1) | .«ERROR '.' %» field0 => some (expressionNonBrace.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expressionNonBrace.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expressionNonBrace.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expressionNonBrace.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expressionNonBrace.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expressionNonBrace.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expressionNonBrace.«`( % `)» field0) | _ => none


def «$expressionNonBrace_as_expression:case_14:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option callExpressionNonBrace) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionNonBrace.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionNonBrace.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «$expressionNonBrace_as_expression:case_14:downcast:1» (arg0 : callTargetNonBrace) : (_root_.Option namedType) := match arg0 with | ._TID field0 => some (namedType._TID field0) | .«_TID '.' %» field0 => some (namedType.«_TID '.' %» field0) | .«% `< % `>» field0 field1 => some (namedType.«% `< % `>» field0 field1) | _ => none


def «$expressionNonBrace_as_expression:case_15:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option callExpressionNonBrace) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionNonBrace.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionNonBrace.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «$expressionNonBrace_as_expression:case_16:downcast:0» (arg0 : expressionNonBrace) : (_root_.Option parenthesizedExpression) := match arg0 with | .«`( % `)» field0 => some (parenthesizedExpression.«`( % `)» field0) | _ => none


def «$expression_as_expressionNonBrace:case_1:downcast:0» (arg0 : expression) : (_root_.Option literalExpression) := match arg0 with | .TRUE => some (literalExpression.TRUE) | .FALSE => some (literalExpression.FALSE) | .D field0 => some (literalExpression.D field0) | .«% W %» field0 field1 => some (literalExpression.«% W %» field0 field1) | .«% S %» field0 field1 => some (literalExpression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (literalExpression.«'"' % '"'» field0) | _ => none


def «$expression_as_expressionNonBrace:case_2:downcast:0» (arg0 : expression) : (_root_.Option referenceExpression) := match arg0 with | ._ID field0 => some (referenceExpression._ID field0) | .APPLY => some (referenceExpression.APPLY) | .KEY => some (referenceExpression.KEY) | .ACTIONS => some (referenceExpression.ACTIONS) | .STATE => some (referenceExpression.STATE) | .ENTRIES => some (referenceExpression.ENTRIES) | .TYPE => some (referenceExpression.TYPE) | .PRIORITY => some (referenceExpression.PRIORITY) | .«_ID '.' %» field0 => some (referenceExpression.«_ID '.' %» field0) | .THIS => some (referenceExpression.THIS) | _ => none


def «$expression_as_expressionNonBrace:case_3:downcast:0» (arg0 : expression) : (_root_.Option unaryExpression) := match arg0 with | .«% %» field0 field1 => some (unaryExpression.«% %» field0 field1) | _ => none


def «$expression_as_expressionNonBrace:case_4:downcast:0» (arg0 : expression) : (_root_.Option binaryExpression) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpression.«% % %» field0 field1 field2) | _ => none


def «$expression_as_expressionNonBrace:case_5:downcast:0» (arg0 : expression) : (_root_.Option ternaryExpression) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpression.«% '?' % ':' %» field0 field1 field2) | _ => none


def «$expression_as_expressionNonBrace:case_6:downcast:0» (arg0 : expression) : (_root_.Option castExpression) := match arg0 with | .«`( % `) %» field0 field1 => some (castExpression.«`( % `) %» field0 field1) | _ => none


def «$expression_as_expressionNonBrace:case_7:downcast:0» (arg0 : expression) : (_root_.Option errorAccessExpression) := match arg0 with | .«ERROR '.' %» field0 => some (errorAccessExpression.«ERROR '.' %» field0) | _ => none


def «$expression_as_expressionNonBrace:case_8:downcast:0» (arg0 : expression) : (_root_.Option memberAccessExpression) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpression.«% '.' %» field0 field1) | _ => none


def «$expression_as_expressionNonBrace:case_8:downcast:1» (arg0 : memberAccessBase) : (_root_.Option prefixedTypeName) := match arg0 with | ._TID field0 => some (prefixedTypeName._TID field0) | .«_TID '.' %» field0 => some (prefixedTypeName.«_TID '.' %» field0) | _ => none


def «$expression_as_expressionNonBrace:case_9:downcast:0» (arg0 : expression) : (_root_.Option memberAccessExpression) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpression.«% '.' %» field0 field1) | _ => none


def «$expression_as_expressionNonBrace:case_9:downcast:1» (arg0 : memberAccessBase) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «$expression_as_expressionNonBrace:case_10:downcast:0» (arg0 : expression) : (_root_.Option indexAccessExpression) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpression.«% `[ % `]» field0 field1) | _ => none


def «$expression_as_expressionNonBrace:case_11:downcast:0» (arg0 : expression) : (_root_.Option sliceAccessExpression) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpression.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «$expression_as_expressionNonBrace:case_12:downcast:0» (arg0 : expression) : (_root_.Option callExpression) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpression.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «$expression_as_expressionNonBrace:case_12:downcast:1» (arg0 : callTarget) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «$expression_as_expressionNonBrace:case_13:downcast:0» (arg0 : expression) : (_root_.Option callExpression) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpression.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «$expression_as_expressionNonBrace:case_13:downcast:1» (arg0 : callTarget) : (_root_.Option namedType) := match arg0 with | ._TID field0 => some (namedType._TID field0) | .«_TID '.' %» field0 => some (namedType.«_TID '.' %» field0) | .«% `< % `>» field0 field1 => some (namedType.«% `< % `>» field0 field1) | _ => none


def «$expression_as_expressionNonBrace:case_14:downcast:0» (arg0 : expression) : (_root_.Option callExpression) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpression.«% `< % `> `( % `)» field0 field1 field2) | _ => none

end SpecTec
