import SpecTecDecl0079

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

namespace SpecTec

variable [SpecTecExternTypes]

def «Expr_eval:lor-abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:lor-true:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval:lor-false:downcast:0» (arg0 : expressionIR) : (_root_.Option binaryExpressionIR) := match arg0 with | .«% % %» field0 field1 field2 => some (binaryExpressionIR.«% % %» field0 field1 field2) | _ => none


def «Expr_eval:cond-abort:downcast:0» (arg0 : expressionIR) : (_root_.Option ternaryExpressionIR) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpressionIR.«% '?' % ':' %» field0 field1 field2) | _ => none


def «Expr_eval:cond-abort:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:cond-true:downcast:0» (arg0 : expressionIR) : (_root_.Option ternaryExpressionIR) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpressionIR.«% '?' % ':' %» field0 field1 field2) | _ => none


def «Expr_eval:cond-false:downcast:0» (arg0 : expressionIR) : (_root_.Option ternaryExpressionIR) := match arg0 with | .«% '?' % ':' %» field0 field1 field2 => some (ternaryExpressionIR.«% '?' % ':' %» field0 field1 field2) | _ => none


def «Expr_eval:abort_2:downcast:0» (arg0 : expressionIR) : (_root_.Option castExpressionIR) := match arg0 with | .«`( % `) %» field0 field1 => some (castExpressionIR.«`( % `) %» field0 field1) | _ => none


def «Expr_eval:abort_2:downcast:1» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:cont_2:downcast:0» (arg0 : expressionIR) : (_root_.Option castExpressionIR) := match arg0 with | .«`( % `) %» field0 field1 => some (castExpressionIR.«`( % `) %» field0 field1) | _ => none


def «Expr_eval:cont_2:downcast:1» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:invalidHeaderExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option invalidHeaderExpression) := match arg0 with | .«'{#}'» => some (invalidHeaderExpression.«'{#}'») | _ => none


def «Expr_eval:non-default-abort:downcast:0» (arg0 : expressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval:non-default-cont:downcast:0» (arg0 : expressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval:default-abort:downcast:0» (arg0 : expressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval:default-cont:downcast:0» (arg0 : expressionIR) : (_root_.Option sequenceExpressionIR) := match arg0 with | .«SEQ `{ % `}» field0 => some (sequenceExpressionIR.«SEQ `{ % `}» field0) | .«SEQ `{ % ',' '...' `}» field0 => some (sequenceExpressionIR.«SEQ `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval:non-default-abort_2:downcast:0» (arg0 : expressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval:non-default-cont_2:downcast:0» (arg0 : expressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval:default-abort_2:downcast:0» (arg0 : expressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval:default-cont_2:downcast:0» (arg0 : expressionIR) : (_root_.Option recordExpressionIR) := match arg0 with | .«RECORD `{ % `}» field0 => some (recordExpressionIR.«RECORD `{ % `}» field0) | .«RECORD `{ % ',' '...' `}» field0 => some (recordExpressionIR.«RECORD `{ % ',' '...' `}» field0) | _ => none


def «Expr_eval:errorAccessExpressionIR:downcast:0» (arg0 : expressionIR) : (_root_.Option errorAccessExpressionIR) := match arg0 with | .«ERROR '.' %» field0 => some (errorAccessExpressionIR.«ERROR '.' %» field0) | _ => none


def «Expr_eval:enum:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:enum:downcast:4» (arg0 : typeIR) : (_root_.Option simpleEnumTypeIR) := match arg0 with | .«ENUM % `{ % `}» field0 field1 => some (simpleEnumTypeIR.«ENUM % `{ % `}» field0 field1) | _ => none


def «Expr_eval:serenum:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:serenum:downcast:4» (arg0 : typeIR) : (_root_.Option serializableEnumTypeIR) := match arg0 with | .«ENUM % `< % `> `{ % `}» field0 field1 field2 => some (serializableEnumTypeIR.«ENUM % `< % `> `{ % `}» field0 field1 field2) | _ => none


def «Expr_eval:abort_3:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:abort_3:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval:abort_3:downcast:2» (arg0 : expressionResult) : (_root_.Option abortResult) := match arg0 with | .EXIT => some (abortResult.EXIT) | .REJECT field0 => some (abortResult.REJECT field0) | _ => none


def «Expr_eval:stack-size:downcast:0» (arg0 : expressionIR) : (_root_.Option memberAccessExpressionIR) := match arg0 with | .«% '.' %» field0 field1 => some (memberAccessExpressionIR.«% '.' %» field0 field1) | _ => none


def «Expr_eval:stack-size:downcast:1» (arg0 : memberAccessBaseIR) : (_root_.Option typedExpressionIR) := match arg0 with | .«% '#' %» field0 field1 => some (typedExpressionIR.«% '#' %» field0 field1) | _ => none


def «Expr_eval:stack-size:downcast:2» (arg0 : expressionResult) : (_root_.Option (continueResult value)) := match arg0 with | ._CONT field0 => some (continueResult._CONT field0) | _ => none


def «Expr_eval:stack-size:downcast:3» (arg0 : value) : (_root_.Option headerStackValue) := match arg0 with | .«HEADER_STACK `[ % `( % `) `]» field0 field1 => some (headerStackValue.«HEADER_STACK `[ % `( % `) `]» field0 field1) | _ => none

end SpecTec
