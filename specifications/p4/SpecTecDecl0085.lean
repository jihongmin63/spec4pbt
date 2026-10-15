import SpecTecDecl0084

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Lvalue_write:header-union-replace-valid-header:downcast:0» (arg0 : value) : (_root_.Option headerUnionValue) := match arg0 with | .«HEADER_UNION % `{ % `}» field0 field1 => some (headerUnionValue.«HEADER_UNION % `{ % `}» field0 field1) | _ => none


def «Lvalue_write:header-union-replace-valid-header:downcast:6» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «Lvalue_write:header-union-replace-valid-header:downcast:8» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «Lvalue_write:array-in-bounds:downcast:0» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Lvalue_write:array-in-bounds:downcast:1» (arg0 : value) : (_root_.Option arrayValue) := match arg0 with | .«ARRAY `[ % `]» field0 => some (arrayValue.«ARRAY `[ % `]» field0) | _ => none


def «Lvalue_write:array-out-of-bounds:downcast:0» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Lvalue_write:array-out-of-bounds:downcast:1» (arg0 : value) : (_root_.Option arrayValue) := match arg0 with | .«ARRAY `[ % `]» field0 => some (arrayValue.«ARRAY `[ % `]» field0) | _ => none


def «Lvalue_write:stack-in-bounds:downcast:0» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Lvalue_write:stack-in-bounds:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Lvalue_write:stack-out-of-bounds:downcast:0» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Lvalue_write:stack-out-of-bounds:downcast:1» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


inductive callResult : Type where
  | EXIT : callResult
  | REJECT : errorValue → callResult
  | RETURN : (_root_.Option value) → callResult
deriving _root_.DecidableEq


def «Expr_eval:callee-cont-call-abort:downcast:2» (arg0 : callResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:callee-cont-call-return:downcast:2» (arg0 : callResult) : (_root_.Option returnResult) := match arg0 with | .RETURN field0 => some (returnResult.RETURN field0) | _ => none


inductive forBreakResult : Type where
  | BREAK : forBreakResult
deriving _root_.DecidableEq


inductive forContinueResult : Type where
  | CONTINUE : forContinueResult
deriving _root_.DecidableEq


inductive forResult : Type where
  | BREAK : forResult
  | CONTINUE : forResult
deriving _root_.DecidableEq


inductive statementResult : Type where
  | _EMPTY : statementResult
  | EXIT : statementResult
  | REJECT : errorValue → statementResult
  | RETURN : (_root_.Option value) → statementResult
  | BREAK : statementResult
  | CONTINUE : statementResult
deriving _root_.DecidableEq


def «Stmt_eval:emptyStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option emptyStatement) := match arg0 with | .«';'» => some (emptyStatement.«';'») | _ => none


def «Stmt_eval:typedLvalueIR-abort:downcast:0» (arg0 : statementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «Stmt_eval:typedLvalueIR-abort:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Stmt_eval:typedLvalueIR-cont-eq-typedExpressionIR-abort:downcast:0» (arg0 : statementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «Stmt_eval:typedLvalueIR-cont-eq-typedExpressionIR-abort:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Stmt_eval:typedLvalueIR-cont-eq-typedExpressionIR-abort:downcast:2» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Stmt_eval:typedLvalueIR-cont-compound-typedExpressionIR-abort:downcast:0» (arg0 : statementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «Stmt_eval:typedLvalueIR-cont-compound-typedExpressionIR-abort:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Stmt_eval:typedLvalueIR-cont-compound-typedExpressionIR-abort:downcast:2» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Stmt_eval:typedLvalueIR-cont-eq-typedExpressionIR-cont:downcast:0» (arg0 : statementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «Stmt_eval:typedLvalueIR-cont-eq-typedExpressionIR-cont:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Stmt_eval:typedLvalueIR-cont-eq-typedExpressionIR-cont:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Stmt_eval:typedLvalueIR-cont-compound-typedExpressionIR-cont:downcast:0» (arg0 : statementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «Stmt_eval:typedLvalueIR-cont-compound-typedExpressionIR-cont:downcast:1» (arg0 : storageReferenceResult) : (_root_.Option (continueResult (_root_.Option storageReference))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none

end SpecTec
