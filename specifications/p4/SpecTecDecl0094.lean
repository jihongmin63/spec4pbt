import SpecTecDecl0093

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Eval_keyset_simple:cont-objectReferenceValue:downcast:4» (arg0 : object) : (_root_.Option valueSetObject) := match arg0 with | .«VALUE_SET `{ % `( % `) `}» field0 field1 => some (valueSetObject.«VALUE_SET `{ % `( % `) `}» field0 field1) | _ => none


def «Eval_keyset_simple:left-abort:downcast:0» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Eval_keyset_simple:left-cont-right-abort:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Eval_keyset_simple:left-cont-right-abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Eval_keyset_simple:left-cont-right-cont:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Eval_keyset_simple:left-cont-right-cont:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Eval_keyset_simple:left-abort_2:downcast:0» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Eval_keyset_simple:left-cont-right-abort_2:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Eval_keyset_simple:left-cont-right-abort_2:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Eval_keyset_simple:left-cont-right-cont_2:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Eval_keyset_simple:left-cont-right-cont_2:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Eval_keysets_simple:cons-head-abort:downcast:0» (arg0 : simpleKeysetExpressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Eval_keysets_simple:cons-head-cont-tail-abort:downcast:0» (arg0 : simpleKeysetExpressionResult) : (_root_.Option (continueResult setValue)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Eval_keysets_simple:cons-head-cont-tail-abort:downcast:1» (arg0 : keysetExpressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Eval_keysets_simple:cons-head-cont-tail-cont:downcast:0» (arg0 : simpleKeysetExpressionResult) : (_root_.Option (continueResult setValue)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Eval_keysets_simple:cons-head-cont-tail-cont:downcast:1» (arg0 : keysetExpressionResult) : (_root_.Option (continueResult (_root_.List setValue))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ForUpdateStmts_eval:cons-head-exit:downcast:0» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «ForUpdateStmts_eval:cons-head-cont:downcast:0» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «ForInitStmt_eval:variableDeclarationIR-initializer-abort:downcast:0» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «ForInitStmt_eval:variableDeclarationIR-initializer-cont:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ForInitStmt_eval:forUpdateStatementIR:downcast:0» (arg0 : forInitStatementIR) : (_root_.Option forUpdateStatementIR) := match arg0 with | .«% `< % `> `( % `)» field0 field1 field2 => some (forUpdateStatementIR.«% `< % `> `( % `)» field0 field1 field2) | .«% % %» field0 field1 field2 => some (forUpdateStatementIR.«% % %» field0 field1 field2) | _ => none


def «ForInitStmts_eval:cons-head-abort:downcast:0» (arg0 : statementResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «ForInitStmts_eval:cons-head-cont:downcast:0» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «ForThreeClauseStmt_eval:cond-abort:downcast:0» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «ForThreeClauseStmt_eval:cond-true-loop-abort:downcast:0» (arg0 : statementResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «ForThreeClauseStmt_eval:cond-true-loop-return:downcast:0» (arg0 : statementResult) : (_root_.Option returnResult) := match arg0 with | .RETURN field0 => some (returnResult.RETURN field0) | _ => none


def «ForThreeClauseStmt_eval:cond-true-loop-break:downcast:0» (arg0 : statementResult) : (_root_.Option forBreakResult) := match arg0 with | .BREAK => some (forBreakResult.BREAK) | _ => none


def «ForThreeClauseStmt_eval:cond-true-loop-cont-update-exit:downcast:0» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «ForThreeClauseStmt_eval:cond-true-loop-cont-update-cont:downcast:0» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «ForCollectionExpr_eval:abort:downcast:0» (arg0 : forCollectionExpressionIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «ForCollectionExpr_eval:abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «ForCollectionExpr_eval:list:downcast:0» (arg0 : forCollectionExpressionIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none

end SpecTec
