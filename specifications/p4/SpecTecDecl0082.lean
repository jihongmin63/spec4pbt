import SpecTecDecl0081

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Expr_eval:tableMetadataStructValue-action_run:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:tableMetadataStructValue-action_run:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval:tableMetadataStructValue-action_run:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:tableMetadataStructValue-action_run:downcast:3» (arg0 : value) : (_root_.Option tableMetadataStructValue) := match arg0 with | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3 => some (tableMetadataStructValue.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3) | _ => none


def «Expr_eval:abort_4:downcast:0» (arg0 : expressionIR) : (_root_.Option indexAccessExpressionIR) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpressionIR.«% `[ % `]» field0 field1) | _ => none


def «Expr_eval:tuple:downcast:0» (arg0 : expressionIR) : (_root_.Option indexAccessExpressionIR) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpressionIR.«% `[ % `]» field0 field1) | _ => none


def «Expr_eval:tuple:downcast:2» (arg0 : value) : (_root_.Option tupleValue) := match arg0 with | .«TUPLE `( % `)» field0 => some (tupleValue.«TUPLE `( % `)» field0) | _ => none


def «Expr_eval:tuple:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Expr_eval:array:downcast:0» (arg0 : expressionIR) : (_root_.Option indexAccessExpressionIR) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpressionIR.«% `[ % `]» field0 field1) | _ => none


def «Expr_eval:array:downcast:2» (arg0 : value) : (_root_.Option arrayValue) := match arg0 with | .«ARRAY `[ % `]» field0 => some (arrayValue.«ARRAY `[ % `]» field0) | _ => none


def «Expr_eval:array:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Expr_eval:headerStack:downcast:0» (arg0 : expressionIR) : (_root_.Option indexAccessExpressionIR) := match arg0 with | .«% `[ % `]» field0 field1 => some (indexAccessExpressionIR.«% `[ % `]» field0 field1) | _ => none


def «Expr_eval:headerStack:downcast:2» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Expr_eval:headerStack:downcast:3» (arg0 : value) : (_root_.Option integerValue) := match arg0 with | .D field0 => some (integerValue.D field0) | .«% W %» field0 field1 => some (integerValue.«% W %» field0 field1) | .«% S %» field0 field1 => some (integerValue.«% S %» field0 field1) | .«% '.' % V %» field0 field1 field2 => some (integerValue.«% '.' % V %» field0 field1 field2) | _ => none


def «Expr_eval:abort_5:downcast:0» (arg0 : expressionIR) : (_root_.Option sliceAccessExpressionIR) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpressionIR.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «Expr_eval:cont-range:downcast:0» (arg0 : expressionIR) : (_root_.Option sliceAccessExpressionIR) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpressionIR.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «Expr_eval:cont-offset:downcast:0» (arg0 : expressionIR) : (_root_.Option sliceAccessExpressionIR) := match arg0 with | .«% `[ % % % `]» field0 field1 field2 field3 => some (sliceAccessExpressionIR.«% `[ % % % `]» field0 field1 field2 field3) | _ => none


def «Expr_eval:callee-abort:downcast:0» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_eval:callee-cont-call-abort:downcast:0» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_eval:callee-cont-call-return:downcast:0» (arg0 : expressionIR) : (_root_.Option callExpressionIR) := match arg0 with | .«% `( % `)» field0 field1 => some (callExpressionIR.«% `( % `)» field0 field1) | .«% `< % `> `( % `)» field0 field1 field2 => some (callExpressionIR.«% `< % `> `( % `)» field0 field1 field2) | _ => none


def «Expr_eval:parenthesizedExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option parenthesizedExpressionIR) := match arg0 with | .«`( % `)» field0 => some (parenthesizedExpressionIR.«`( % `)» field0) | _ => none


inductive expressionListResult : Type where
  | _CONT : (_root_.List value) → expressionListResult
  | EXIT : expressionListResult
  | REJECT : errorValue → expressionListResult
deriving _root_.DecidableEq


def «Expr_eval:non-short-circuit-abort:downcast:1» (arg0 : expressionListResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:non-short-circuit-cont:downcast:1» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:non-default-abort:downcast:1» (arg0 : expressionListResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:non-default-cont:downcast:1» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:default-abort:downcast:1» (arg0 : expressionListResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:default-cont:downcast:1» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:non-default-abort_2:downcast:3» (arg0 : expressionListResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:non-default-cont_2:downcast:3» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:default-abort_2:downcast:3» (arg0 : expressionListResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:default-cont_2:downcast:3» (arg0 : expressionListResult) : (_root_.Option (continueResult (_root_.List value))) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none

end SpecTec
