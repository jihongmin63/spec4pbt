import SpecTecDecl0085

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Stmt_eval:typedLvalueIR-cont-compound-typedExpressionIR-cont:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Stmt_eval:callee-abort:downcast:0» (arg0 : statementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «Stmt_eval:callee-cont-call-abort:downcast:0» (arg0 : statementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «Stmt_eval:callee-cont-call-abort:downcast:2» (arg0 : callResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Stmt_eval:callee-cont-call-return:downcast:0» (arg0 : statementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «Stmt_eval:callee-cont-call-return:downcast:2» (arg0 : callResult) : (_root_.Option returnResult) := match arg0 with | .RETURN field0 => some (returnResult.RETURN field0) | _ => none


def «Stmt_eval:non-expression:downcast:0» (arg0 : statementIR) : (_root_.Option returnStatementIR) := match arg0 with | .«RETURN ';'» => some (returnStatementIR.«RETURN ';'») | .«RETURN % ';'» field0 => some (returnStatementIR.«RETURN % ';'» field0) | _ => none


def «Stmt_eval:expression-abort:downcast:0» (arg0 : statementIR) : (_root_.Option returnStatementIR) := match arg0 with | .«RETURN ';'» => some (returnStatementIR.«RETURN ';'») | .«RETURN % ';'» field0 => some (returnStatementIR.«RETURN % ';'» field0) | _ => none


def «Stmt_eval:expression-abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Stmt_eval:expression-cont:downcast:0» (arg0 : statementIR) : (_root_.Option returnStatementIR) := match arg0 with | .«RETURN ';'» => some (returnStatementIR.«RETURN ';'») | .«RETURN % ';'» field0 => some (returnStatementIR.«RETURN % ';'» field0) | _ => none


def «Stmt_eval:expression-cont:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Stmt_eval:exitStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option exitStatement) := match arg0 with | .«EXIT ';'» => some (exitStatement.«EXIT ';'») | _ => none


def «Stmt_eval:blockStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option blockStatementIR) := match arg0 with | .«% `{ % `}» field0 field1 => some (blockStatementIR.«% `{ % `}» field0 field1) | _ => none


def «Stmt_eval:non-else-abort:downcast:0» (arg0 : statementIR) : (_root_.Option conditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (conditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (conditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «Stmt_eval:non-else-abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Stmt_eval:non-else-cont-true:downcast:0» (arg0 : statementIR) : (_root_.Option conditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (conditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (conditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «Stmt_eval:non-else-cont-false:downcast:0» (arg0 : statementIR) : (_root_.Option conditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (conditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (conditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «Stmt_eval:else-abort:downcast:0» (arg0 : statementIR) : (_root_.Option conditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (conditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (conditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «Stmt_eval:else-abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Stmt_eval:else-cont-true:downcast:0» (arg0 : statementIR) : (_root_.Option conditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (conditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (conditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «Stmt_eval:else-cont-false:downcast:0» (arg0 : statementIR) : (_root_.Option conditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (conditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (conditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «Stmt_eval:init-abort:downcast:0» (arg0 : statementIR) : (_root_.Option forStatementIR) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_eval:init-abort:downcast:2» (arg0 : statementResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Stmt_eval:init-cont:downcast:0» (arg0 : statementIR) : (_root_.Option forStatementIR) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_eval:init-cont:downcast:2» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «Stmt_eval:no-annotations-collection-abort:downcast:0» (arg0 : statementIR) : (_root_.Option forStatementIR) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_eval:no-annotations-collection-abort:downcast:2» (arg0 : expressionListResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Stmt_eval:no-annotations-collection-loop:downcast:0» (arg0 : statementIR) : (_root_.Option forStatementIR) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_eval:no-annotations-collection-loop:downcast:2» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Stmt_eval:annotations:downcast:0» (arg0 : statementIR) : (_root_.Option forStatementIR) := match arg0 with | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (forStatementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (forStatementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | _ => none


def «Stmt_eval:breakStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option breakStatement) := match arg0 with | .«BREAK ';'» => some (breakStatement.«BREAK ';'») | _ => none


def «Stmt_eval:continueStatementIR:downcast:0» (arg0 : statementIR) : (_root_.Option continueStatement) := match arg0 with | .«CONTINUE ';'» => some (continueStatement.«CONTINUE ';'») | _ => none

end SpecTec
