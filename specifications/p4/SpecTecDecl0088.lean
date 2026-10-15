import SpecTecDecl0087

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «ParserBlockElementStmt_eval:variableDeclarationIR-reject:downcast:0» (arg0 : parserBlockElementStatementIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserBlockElementStmt_eval:variableDeclarationIR-empty:downcast:0» (arg0 : parserBlockElementStatementIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserBlockElementStmt_eval:statementIR:downcast:0» (arg0 : parserBlockElementStatementIR) : (_root_.Option parserStatementIR) := match arg0 with | .«';'» => some (parserStatementIR.«';'») | .«% % % ';'» field0 field1 field2 => some (parserStatementIR.«% % % ';'» field0 field1 field2) | .«% `< % `> `( % `) ';'» field0 field1 field2 => some (parserStatementIR.«% `< % `> `( % `) ';'» field0 field1 field2) | .«% '.' APPLY `( % `) ';'» field0 field1 => some (parserStatementIR.«% '.' APPLY `( % `) ';'» field0 field1) | .«% `{ % `}» field0 field1 => some (parserStatementIR.«% `{ % `}» field0 field1) | .«IF `( % `) %» field0 field1 => some (parserStatementIR.«IF `( % `) %» field0 field1) | .«IF `( % `) % ELSE %» field0 field1 field2 => some (parserStatementIR.«IF `( % `) % ELSE %» field0 field1 field2) | _ => none


def «ParserBlockElementStmtList_eval:cons-head-cont:downcast:0» (arg0 : parserStatementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


inductive transitionResult : Type where
  | ACCEPT : transitionResult
  | REJECT : errorValue → transitionResult
  | STATE : id → transitionResult
deriving _root_.DecidableEq


def «ParserSelect_eval:reject:downcast:0» (arg0 : expressionListResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «ParserSelect_eval:cont-selectCaseListIR-reject:downcast:0» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ParserSelect_eval:no-match:downcast:0» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ParserSelect_eval:match:downcast:0» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ParserTransition_eval:selectExpressionIR:downcast:0» (arg0 : stateExpressionIR) : (_root_.Option selectExpressionIR) := match arg0 with | .«SELECT `( % `) `{ % `}» field0 field1 => some (selectExpressionIR.«SELECT `( % `) `{ % `}» field0 field1) | _ => none


def «ParserState_eval:reject:downcast:1» (arg0 : parserStatementResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «ParserState_eval:cont:downcast:1» (arg0 : parserStatementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «ParserState_trans:accept:downcast:1» (arg0 : transitionResult) : (_root_.Option acceptTransitionResult) := match arg0 with | .ACCEPT => some (acceptTransitionResult.ACCEPT) | _ => none


def «ParserState_trans:reject:downcast:1» (arg0 : transitionResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «ParserState_trans:state:downcast:1» (arg0 : transitionResult) : (_root_.Option stateTransitionResult) := match arg0 with | .STATE field0 => some (stateTransitionResult.STATE field0) | _ => none


abbrev parserDeclarationResult : Type := parserStatementResult


def «ParserLocalDecl_eval:constantDeclarationIR:downcast:0» (arg0 : parserLocalDeclarationIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserLocalDecl_eval:reject:downcast:0» (arg0 : parserLocalDeclarationIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserLocalDecl_eval:cont:downcast:0» (arg0 : parserLocalDeclarationIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ParserLocalDecls_eval:cons-reject:downcast:0» (arg0 : parserStatementResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «ParserLocalDecls_eval:cons-cont:downcast:0» (arg0 : parserStatementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


inductive tableResult : Type where
  | EXIT : tableResult
  | RETURN : (_root_.Option value) → tableResult
deriving _root_.DecidableEq


def «Table_eval:keys-cont-matches-cont-action-exit:downcast:3» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


def «Table_eval:keys-cont-matches-cont-action-cont:downcast:3» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


inductive controlBodyResult : Type where
  | EXIT : controlBodyResult
  | RETURN : (_root_.Option value) → controlBodyResult
deriving _root_.DecidableEq


def «ControlBody_eval:cont:downcast:0» (arg0 : statementResult) : (_root_.Option continueEmptyResult) := match arg0 with | ._EMPTY => some (continueEmptyResult._EMPTY) | _ => none


def «ControlBody_eval:exit:downcast:0» (arg0 : statementResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none


inductive controlLocalDeclarationResult : Type where
  | _EMPTY : controlLocalDeclarationResult
  | EXIT : controlLocalDeclarationResult
deriving _root_.DecidableEq


def «ControlLocalDecl_eval:constantDeclarationIR:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option constantDeclarationIR) := match arg0 with | .«% CONST % % % ';'» field0 field1 field2 field3 => some (constantDeclarationIR.«% CONST % % % ';'» field0 field1 field2 field3) | _ => none


def «ControlLocalDecl_eval:exit:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ControlLocalDecl_eval:cont:downcast:0» (arg0 : controlLocalDeclarationIR) : (_root_.Option variableDeclarationIR) := match arg0 with | .«% % % % ';'» field0 field1 field2 field3 => some (variableDeclarationIR.«% % % % ';'» field0 field1 field2 field3) | _ => none


def «ControlLocalDecls_eval:cons-head-exit:downcast:0» (arg0 : controlLocalDeclarationResult) : (_root_.Option exitResult) := match arg0 with | .EXIT => some (exitResult.EXIT) | _ => none

end SpecTec
