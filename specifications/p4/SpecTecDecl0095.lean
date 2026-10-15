import SpecTecDecl0094

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «ForCollectionExpr_eval:list:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ForCollectionExpr_eval:list:downcast:2» (arg0 : value) : (_root_.Option listValue) := match arg0 with | .«LIST `[ % `]» field0 => some (listValue.«LIST `[ % `]» field0) | _ => none


def «ForCollectionExpr_eval:array:downcast:0» (arg0 : forCollectionExpressionIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «ForCollectionExpr_eval:array:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ForCollectionExpr_eval:array:downcast:2» (arg0 : value) : (_root_.Option arrayValue) := match arg0 with | .«ARRAY `[ % `]» field0 => some (arrayValue.«ARRAY `[ % `]» field0) | _ => none


def «ForCollectionExpr_eval:header-stack:downcast:0» (arg0 : forCollectionExpressionIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «ForCollectionExpr_eval:header-stack:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ForCollectionExpr_eval:header-stack:downcast:2» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «ForCollectionExpr_eval:left-abort:downcast:0» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «ForCollectionExpr_eval:left-cont-right-abort:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ForCollectionExpr_eval:left-cont-right-abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «ForCollectionExpr_eval:left-cont-right-cont:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ForCollectionExpr_eval:left-cont-right-cont:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ForInStmt_eval:cons-loop-abort:downcast:1» (arg0 : statementResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «ForInStmt_eval:cons-loop-return:downcast:1» (arg0 : statementResult) : (_root_.Option returnResult) := match arg0 with | .RETURN field0 => some (returnResult.RETURN field0) | _ => none


def «ForInStmt_eval:cons-loop-break:downcast:1» (arg0 : statementResult) : (_root_.Option forBreakResult) := match arg0 with | .BREAK => some (forBreakResult.BREAK) | _ => none


def «$match_switchLabelIR_table:case_2:downcast:0» (arg0 : switchLabelIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «$match_switchLabelIR_table:case_2:downcast:1» (arg0 : expressionIR) : (_root_.Option prefixedNameIR) := match arg0 with | ._BARE field0 => some (prefixedNameIR._BARE field0) | .«'.' %» field0 => some (prefixedNameIR.«'.' %» field0) | _ => none


def «SwitchLabel_general_eval:typedExpressionIR:downcast:0» (arg0 : switchLabelIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «$match_switchLabelIR_general:case_1:downcast:0» (arg0 : value) : (_root_.Option defaultValue) := match arg0 with | .DEFAULT => some (defaultValue.DEFAULT) | _ => none


def «SwitchCases_general_eval:cons-non-fallthrough-match:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «SwitchCases_general_eval:cons-non-fallthrough-no-match:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «SwitchCases_general_eval:cons-fallthrough-match:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «SwitchCases_general_eval:cons-fallthrough-match-no-block:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «SwitchCases_general_eval:cons-fallthrough-no-match:downcast:0» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


inductive selectCaseMatchResult : Type where
  | _CONT : (_root_.Option nameIR) → selectCaseMatchResult
  | REJECT : errorValue → selectCaseMatchResult
deriving _root_.DecidableEq


def «ParserSelect_eval:cont-selectCaseListIR-reject:downcast:1» (arg0 : selectCaseMatchResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «ParserSelect_eval:no-match:downcast:1» (arg0 : selectCaseMatchResult) : (_root_.Option (continueResult (_root_.Option _root_.String))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «ParserSelect_eval:match:downcast:1» (arg0 : selectCaseMatchResult) : (_root_.Option (continueResult (_root_.Option _root_.String))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «SelectCase_match:reject:downcast:0» (arg0 : keysetExpressionResult) : (_root_.Option rejectTransitionResult) := match arg0 with | .REJECT field0 => some (rejectTransitionResult.REJECT field0) | _ => none


def «SelectCase_match:no-match:downcast:0» (arg0 : keysetExpressionResult) : (_root_.Option (continueResult (_root_.List setValue))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «SelectCase_match:match:downcast:0» (arg0 : keysetExpressionResult) : (_root_.Option (continueResult (_root_.List setValue))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none

end SpecTec
