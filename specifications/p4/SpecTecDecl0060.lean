import SpecTecDecl0059

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Expr_ok:offset-lo-non-lctk:downcast:12» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Expr_ok:non-typeArgumentList-static_assert:downcast:0» (arg0 : expression) : (_root_.Option callExpression) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpression.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_ok:non-typeArgumentList-static_assert:downcast:1» (arg0 : callTarget) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «Expr_ok:non-typeArgumentList:downcast:0» (arg0 : expression) : (_root_.Option callExpression) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpression.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_ok:non-typeArgumentList:downcast:1» (arg0 : callTarget) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «Expr_ok:typeArgumentList:downcast:0» (arg0 : expression) : (_root_.Option callExpression) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpression.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_ok:prefixedTypeName:downcast:0» (arg0 : expression) : (_root_.Option callExpression) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpression.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_ok:prefixedTypeName:downcast:1» (arg0 : callTarget) : (_root_.Option prefixedTypeName) := match arg0 with | ._TID field0 => some (prefixedTypeName._TID field0) | .«_TID '.' %» field0 => some (prefixedTypeName.«_TID '.' %» field0) | _ => none


def «Expr_ok:specializedType:downcast:0» (arg0 : expression) : (_root_.Option callExpression) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpression.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_ok:specializedType:downcast:1» (arg0 : callTarget) : (_root_.Option specializedType) := match arg0 with | .«% `< % `>» field0 field1 => some (specializedType.«% `< % `>» field0 field1) | _ => none


def «Expr_ok:parenthesizedExpression:downcast:0» (arg0 : expression) : (_root_.Option parenthesizedExpression) := match arg0 with | .«`( % `)» field0 => some (parenthesizedExpression.«`( % `)» field0) | _ => none


def «Argument_ok:expression:downcast:0» (arg0 : argument) : (_root_.Option expression) := match arg0 with | .TRUE => some (expression.TRUE) | .FALSE => some (expression.FALSE) | .D field0 => some (expression.D field0) | .«% W %» field0 field1 => some (expression.«% W %» field0 field1) | .«% S %» field0 field1 => some (expression.«% S %» field0 field1) | .«'"' % '"'» field0 => some (expression.«'"' % '"'» field0) | ._ID field0 => some (expression._ID field0) | .APPLY => some (expression.APPLY) | .KEY => some (expression.KEY) | .ACTIONS => some (expression.ACTIONS) | .STATE => some (expression.STATE) | .ENTRIES => some (expression.ENTRIES) | .TYPE => some (expression.TYPE) | .PRIORITY => some (expression.PRIORITY) | .«_ID '.' %» field0 => some (expression.«_ID '.' %» field0) | .THIS => some (expression.THIS) | .«'...'» => some (expression.«'...'») | .«% %» field0 field1 => some (expression.«% %» field0 field1) | .«% % %» field0 field1 field2 => some (expression.«% % %» field0 field1 field2) | .«% '?' % ':' %» field0 field1 field2 => some (expression.«% '?' % ':' %» field0 field1 field2) | .«`( % `) %» field0 field1 => some (expression.«`( % `) %» field0 field1) | .«'{#}'» => some (expression.«'{#}'») | .«`{ % % `}» field0 field1 => some (expression.«`{ % % `}» field0 field1) | .«ERROR '.' %» field0 => some (expression.«ERROR '.' %» field0) | .«% '.' %» field0 field1 => some (expression.«% '.' %» field0 field1) | .«% `[ % `]» field0 field1 => some (expression.«% `[ % `]» field0 field1) | .«% `[ % % % `]» field0 field1 field2 field3 => some (expression.«% `[ % % % `]» field0 field1 field2 field3) | .«% `( % `)» field0 field1 => some (expression.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (expression.«% `< % `> `( % `)» field0 field1 field2) | .«`( % `)» field0 => some (expression.«`( % `)» field0) | _ => none


def «Lvalue_ok:referenceExpression:downcast:0» (arg0 : lvalue) : (_root_.Option prefixedNonTypeName) := match arg0 with | ._ID field0 => some (prefixedNonTypeName._ID field0) | .APPLY => some (prefixedNonTypeName.APPLY) | .KEY => some (prefixedNonTypeName.KEY) | .ACTIONS => some (prefixedNonTypeName.ACTIONS) | .STATE => some (prefixedNonTypeName.STATE) | .ENTRIES => some (prefixedNonTypeName.ENTRIES) | .TYPE => some (prefixedNonTypeName.TYPE) | .PRIORITY => some (prefixedNonTypeName.PRIORITY) | .«_ID '.' %» field0 => some (prefixedNonTypeName.«_ID '.' %» field0) | _ => none


def «Lvalue_ok:headerStackTypeIR-next-last:downcast:1» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «Lvalue_ok:structTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option structTypeIR) := match arg0 with | .«STRUCT % `< % `> `{ % `}» field0 field1 field2 => some (structTypeIR.«STRUCT % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Lvalue_ok:headerTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option headerTypeIR) := match arg0 with | .«HEADER % `< % `> `{ % `}» field0 field1 field2 => some (headerTypeIR.«HEADER % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Lvalue_ok:headerUnionTypeIR:downcast:1» (arg0 : typeIR) : (_root_.Option headerUnionTypeIR) := match arg0 with | .«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2 => some (headerUnionTypeIR.«HEADER_UNION % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Lvalue_ok:array-lctk:downcast:1» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «Lvalue_ok:array-lctk:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Lvalue_ok:array-non-lctk:downcast:1» (arg0 : typeIR) : (_root_.Option arrayTypeIR) := match arg0 with | .«ARRAY % `[ % `]» field0 field1 => some (arrayTypeIR.«ARRAY % `[ % `]» field0 field1) | _ => none


def «Lvalue_ok:headerStack-lctk:downcast:1» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «Lvalue_ok:headerStack-lctk:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Lvalue_ok:headerStack-non-lctk:downcast:1» (arg0 : typeIR) : (_root_.Option headerStackTypeIR) := match arg0 with | .«HEADER_STACK % `[ % `]» field0 field1 => some (headerStackTypeIR.«HEADER_STACK % `[ % `]» field0 field1) | _ => none


def «Lvalue_ok:range:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Lvalue_ok:range:downcast:5» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Lvalue_ok:offset:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Stmt_ok:emptyStatement:downcast:0» (arg0 : statement) : (_root_.Option emptyStatement) := match arg0 with | .«';'» => some (emptyStatement.«';'») | _ => none


def «Stmt_ok:eq:downcast:0» (arg0 : statement) : (_root_.Option assignmentStatement) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatement.«% % % ';'» field0 field1 field2) | _ => none


def «Stmt_ok:compound:downcast:0» (arg0 : statement) : (_root_.Option assignmentStatement) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatement.«% % % ';'» field0 field1 field2) | _ => none


def «Stmt_ok:compound:downcast:4» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Stmt_ok:callStatement-no-typeArgumentList-static_assert:downcast:0» (arg0 : statement) : (_root_.Option callStatement) := match arg0 with | .«% `( % `) ';'» field0 field1 => some (callStatement.«% `( % `) ';'» field0 field1) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatement.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «Stmt_ok:callStatement-no-typeArgumentList:downcast:0» (arg0 : statement) : (_root_.Option callStatement) := match arg0 with | .«% `( % `) ';'» field0 field1 => some (callStatement.«% `( % `) ';'» field0 field1) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatement.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none

end SpecTec
