import SpecTecDecl0086

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Stmt_eval:target-abort:downcast:0» (arg0 : statementIR) : (_root_.Option switchStatementIR) := match arg0 with | .«SWITCH `( % `) `{ % `}» field0 field1 => some (switchStatementIR.«SWITCH `( % `) `{ % `}» field0 field1) | _ => none


def «Stmt_eval:target-abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Stmt_eval:target-cont-table:downcast:0» (arg0 : statementIR) : (_root_.Option switchStatementIR) := match arg0 with | .«SWITCH `( % `) `{ % `}» field0 field1 => some (switchStatementIR.«SWITCH `( % `) `{ % `}» field0 field1) | _ => none


def «Stmt_eval:target-cont-table:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Stmt_eval:target-cont-table:downcast:2» (arg0 : value) : (_root_.Option tableMetadataEnumValue) := match arg0 with | .«TABLE_ENUM % '.' %» field0 field1 => some (tableMetadataEnumValue.«TABLE_ENUM % '.' %» field0 field1) | _ => none


def «Stmt_eval:target-cont-general:downcast:0» (arg0 : statementIR) : (_root_.Option switchStatementIR) := match arg0 with | .«SWITCH `( % `) `{ % `}» field0 field1 => some (switchStatementIR.«SWITCH `( % `) `{ % `}» field0 field1) | _ => none


def «Stmt_eval:target-cont-general:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «BlockElementStmt_eval:constantDeclarationIR:downcast:0» (arg0 : blockElementStatementIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «BlockElementStmt_eval:variableDeclarationIR:downcast:0» (arg0 : blockElementStatementIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «BlockElementStmt_eval:statementIR:downcast:0» (arg0 : blockElementStatementIR) : (_root_.Option statementIR) := match arg0 with | .«';'» => some (statementIR.«';'») | .«% % % ';'» field0 field1 field2 => some (statementIR.«% % % ';'» field0 field1 field2) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (statementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | .«% '.' APPLY `( % `) ';'» field0 field1 => some (statementIR.«% '.' APPLY `( % `) ';'» field0 field1) | .«RETURN ';'» => some (statementIR.«RETURN ';'») | .«RETURN % ';'» field0 => some (statementIR.«RETURN % ';'» field0) | .«EXIT ';'» => some (statementIR.«EXIT ';'») | .«% `{ % `}» field0 field1 => some (statementIR.«% `{ % `}» field0 field1) | .«IF `( % `) %» field0 field1 => some (statementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (statementIR.«IF `( % `) % ELSE %» field0 field1 field2) | .«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4 => some (statementIR.«% FOR `( % ';' % ';' % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4 => some (statementIR.«% FOR `( % % IN % `) %» field0 field1 field2 field3 field4) | .«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5 => some (statementIR.«% FOR `( % % % IN % `) %» field0 field1 field2 field3 field4 field5) | .«BREAK ';'» => some (statementIR.«BREAK ';'») | .«CONTINUE ';'» => some (statementIR.«CONTINUE ';'») | .«SWITCH `( % `) `{ % `}» field0 field1 => some (statementIR.«SWITCH `( % `) `{ % `}» field0 field1) | _ => none


def «BlockElementStmtList_eval:cons-head-cont:downcast:0» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


inductive parserStatementResult : Type where
  | _EMPTY : parserStatementResult
  | REJECT : errorValue → parserStatementResult
deriving _root_.DecidableEq


def «ParserStmt_eval:emptyStatementIR:downcast:0» (arg0 : parserStatementIR) : (_root_.Option emptyStatement) := match arg0 with | .«';'» => some (emptyStatement.«';'») | _ => none


def «ParserStmt_eval:emptyStatementIR:downcast:1» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «ParserStmt_eval:reject:downcast:0» (arg0 : parserStatementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «ParserStmt_eval:reject:downcast:1» (arg0 : statementResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «ParserStmt_eval:cont:downcast:0» (arg0 : parserStatementIR) : (_root_.Option assignmentStatementIR) := match arg0 with | .«% % % ';'» field0 field1 field2 => some (assignmentStatementIR.«% % % ';'» field0 field1 field2) | _ => none


def «ParserStmt_eval:cont:downcast:1» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «ParserStmt_eval:reject_2:downcast:0» (arg0 : parserStatementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «ParserStmt_eval:reject_2:downcast:1» (arg0 : statementResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «ParserStmt_eval:cont_2:downcast:0» (arg0 : parserStatementIR) : (_root_.Option callStatementIR) := match arg0 with | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (callStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | _ => none


def «ParserStmt_eval:cont_2:downcast:1» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «ParserStmt_eval:parserBlockStatementIR:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserBlockStatementIR) := match arg0 with | .«% `{ % `}» field0 field1 => some (parserBlockStatementIR.«% `{ % `}» field0 field1) | _ => none


def «ParserStmt_eval:non-else-reject:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserConditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (parserConditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserConditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserStmt_eval:non-else-reject:downcast:1» (arg0 : expressionResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «ParserStmt_eval:non-else-cont-true:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserConditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (parserConditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserConditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserStmt_eval:non-else-cont-false:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserConditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (parserConditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserConditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserStmt_eval:else-reject:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserConditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (parserConditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserConditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserStmt_eval:else-reject:downcast:1» (arg0 : expressionResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «ParserStmt_eval:else-cont-true:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserConditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (parserConditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserConditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserStmt_eval:else-cont-false:downcast:0» (arg0 : parserStatementIR) : (_root_.Option parserConditionalStatementIR) := match arg0 with | .«IF `( % `) %» field0 field1 => some (parserConditionalStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserConditionalStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserBlockElementStmt_eval:constantDeclarationIR:downcast:0» (arg0 : parserBlockElementStatementIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none

end SpecTec
