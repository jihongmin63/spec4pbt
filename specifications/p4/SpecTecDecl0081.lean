import SpecTecDecl0080

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Expr_eval:stack-last-out-of-bounds:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:stack-last-out-of-bounds:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval:stack-last-out-of-bounds:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:stack-last-out-of-bounds:downcast:3» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Expr_eval:stack-last-in-bounds:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:stack-last-in-bounds:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval:stack-last-in-bounds:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:stack-last-in-bounds:downcast:3» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Expr_eval:stack-lastIndex:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:stack-lastIndex:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval:stack-lastIndex:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:stack-lastIndex:downcast:3» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none


def «Expr_eval:struct:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:struct:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval:struct:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:struct:downcast:3» (arg0 : value) : (_root_.Option structValue) := match arg0 with | .«STRUCT % `{ % `}» field0 field1 => some (structValue.«STRUCT % `{ % `}» field0 field1) | _ => none


def «Expr_eval:header:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:header:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval:header:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:header:downcast:3» (arg0 : value) : (_root_.Option headerValue) := match arg0 with | .«HEADER % `{ % ';' % `}» field0 field1 field2 => some (headerValue.«HEADER % `{ % ';' % `}» field0 field1 field2) | _ => none


def «Expr_eval:headerunion:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:headerunion:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval:headerunion:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:headerunion:downcast:3» (arg0 : value) : (_root_.Option headerUnionValue) := match arg0 with | .«HEADER_UNION % `{ % `}» field0 field1 => some (headerUnionValue.«HEADER_UNION % `{ % `}» field0 field1) | _ => none


def «Expr_eval:tableMetadataStructValue-hit:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:tableMetadataStructValue-hit:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval:tableMetadataStructValue-hit:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:tableMetadataStructValue-hit:downcast:3» (arg0 : value) : (_root_.Option tableMetadataStructValue) := match arg0 with | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3 => some (tableMetadataStructValue.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3) | _ => none


def «Expr_eval:tableMetadataStructValue-miss:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:tableMetadataStructValue-miss:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval:tableMetadataStructValue-miss:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:tableMetadataStructValue-miss:downcast:3» (arg0 : value) : (_root_.Option tableMetadataStructValue) := match arg0 with | .«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3 => some (tableMetadataStructValue.«TABLE_STRUCT % `{ HIT % ';' MISS % ';' ACTION_RUN % ';' `}» field0 field1 field2 field3) | _ => none

end SpecTec
